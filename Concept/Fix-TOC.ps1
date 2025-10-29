# Fix TOC and Numbering for all Markdown files
# PowerShell脚本：修复Markdown文件的目录和序号

param(
    [string]$Path = ".",
    [switch]$DryRun = $false
)

$ErrorActionPreference = "Continue"
$stats = @{
    Total = 0
    Fixed = 0
    Skipped = 0
    Errors = 0
}

$fixedFiles = @()

function Generate-Anchor {
    param([string]$Text)
    
    # 移除特殊字符
    $anchor = $Text -replace '[^\w\s\u4e00-\u9fff_-]', ''
    # 转小写，空格替换为连字符
    $anchor = $anchor.ToLower() -replace '\s+', '-' -replace '_', '-'
    # 移除多余连字符
    $anchor = $anchor -replace '-+', '-' -replace '^-|-$', ''
    
    return $anchor
}

function Extract-Headings {
    param([string[]]$Lines)
    
    $headings = @()
    $inCodeBlock = $false
    
    foreach ($line in $Lines) {
        # 检测代码块
        if ($line -match '^```') {
            $inCodeBlock = -not $inCodeBlock
            continue
        }
        
        if ($inCodeBlock) { continue }
        
        # 匹配标题
        if ($line -match '^(#{1,6})\s+(.+)$') {
            $level = $matches[1].Length
            $text = $matches[2].Trim()
            $anchor = Generate-Anchor $text
            
            $headings += @{
                Level = $level
                Text = $text
                Anchor = $anchor
            }
        }
    }
    
    return $headings
}

function Generate-TOC {
    param([array]$Headings)
    
    if ($Headings.Count -eq 0) { return "" }
    
    $toc = @("## 📋 目录", "")
    
    # 跳过第一个标题（文件标题）
    for ($i = 1; $i -lt $Headings.Count; $i++) {
        $h = $Headings[$i]
        
        # 只包含 2-4 级标题
        if ($h.Level -lt 2 -or $h.Level -gt 4) { continue }
        
        $indent = "  " * ($h.Level - 2)
        $toc += "$indent- [$($h.Text)](#$($h.Anchor))"
    }
    
    $toc += ""
    return $toc -join "`n"
}

function Find-TOC-Section {
    param([string[]]$Lines)
    
    $patterns = @(
        '^\s*##\s*📋\s*目录',
        '^\s*##\s*目录',
        '^\s*##\s*Table of Contents',
        '^\s*##\s*📖\s*目录'
    )
    
    $startLine = -1
    
    for ($i = 0; $i -lt $Lines.Count; $i++) {
        $line = $Lines[$i]
        foreach ($pattern in $patterns) {
            if ($line -match $pattern) {
                $startLine = $i
                break
            }
        }
        if ($startLine -ge 0) { break }
    }
    
    if ($startLine -lt 0) { return $null }
    
    # 查找结束位置
    $endLine = $startLine + 1
    for ($i = $startLine + 1; $i -lt $Lines.Count; $i++) {
        $line = $Lines[$i].Trim()
        
        # 遇到下一个 ## 标题或分隔符
        if ($line -match '^##\s+[^#]' -or ($line -eq '---' -and $i -gt $startLine + 2)) {
            $endLine = $i
            break
        }
    }
    
    return @{
        Start = $startLine
        End = $endLine
    }
}

function Fix-File {
    param([System.IO.FileInfo]$File)
    
    try {
        $content = Get-Content $File.FullName -Raw -Encoding UTF8
        $lines = $content -split "`r?`n"
        
        # 提取标题
        $headings = Extract-Headings $lines
        
        if ($headings.Count -lt 3) {
            return @{
                Action = "skip"
                Reason = "too few headings"
            }
        }
        
        # 生成新目录
        $newTOC = Generate-TOC $headings
        
        if ([string]::IsNullOrEmpty($newTOC)) {
            return @{
                Action = "skip"
                Reason = "no valid headings"
            }
        }
        
        # 查找现有目录
        $tocSection = Find-TOC-Section $lines
        
        if ($tocSection) {
            # 更新现有目录
            $newLines = $lines[0..($tocSection.Start - 1)]
            $newLines += $newTOC -split "`n"
            if ($tocSection.End -lt $lines.Count) {
                $newLines += $lines[$tocSection.End..($lines.Count - 1)]
            }
            
            $newContent = $newLines -join "`n"
            
            if (-not $DryRun) {
                $newContent | Set-Content $File.FullName -Encoding UTF8 -NoNewline
            }
            
            return @{
                Action = "updated"
                Reason = "TOC updated"
            }
        }
        else {
            # 查找插入位置（元数据块之后）
            $insertPos = 0
            $inMetadata = $false
            
            for ($i = 0; $i -lt $lines.Count; $i++) {
                $line = $lines[$i]
                
                if ($i -eq 0 -and $line.Trim() -match '^>') {
                    $inMetadata = $true
                }
                
                if ($inMetadata) {
                    if ($line.Trim() -eq '---') {
                        $insertPos = $i + 1
                        break
                    }
                    if ($line.Trim() -notmatch '^>' -and $line.Trim() -ne '') {
                        $inMetadata = $false
                    }
                }
                
                if ($line -match '^##\s+') {
                    $insertPos = $i
                    break
                }
            }
            
            # 插入新目录
            $newLines = $lines[0..($insertPos - 1)]
            $newLines += ""
            $newLines += "---"
            $newLines += ""
            $newLines += $newTOC -split "`n"
            $newLines += ""
            $newLines += "---"
            $newLines += ""
            if ($insertPos -lt $lines.Count) {
                $newLines += $lines[$insertPos..($lines.Count - 1)]
            }
            
            $newContent = $newLines -join "`n"
            
            if (-not $DryRun) {
                $newContent | Set-Content $File.FullName -Encoding UTF8 -NoNewline
            }
            
            return @{
                Action = "added"
                Reason = "TOC added"
            }
        }
    }
    catch {
        return @{
            Action = "error"
            Reason = $_.Exception.Message
        }
    }
}

# 主处理逻辑
Write-Host "=" * 80
Write-Host "Markdown 目录修复工具"
Write-Host "=" * 80
Write-Host ""

if ($DryRun) {
    Write-Host "【模拟模式】不会实际修改文件" -ForegroundColor Yellow
    Write-Host ""
}

$mdFiles = Get-ChildItem -Path $Path -Filter "*.md" -Recurse | Where-Object {
    $_.FullName -notmatch 'node_modules|\.git|venv|__pycache__'
}

Write-Host "找到 $($mdFiles.Count) 个 Markdown 文件"
Write-Host ""
Write-Host "开始处理..."
Write-Host ""

foreach ($file in $mdFiles) {
    $stats.Total++
    
    $relativePath = $file.FullName.Replace((Get-Location).Path, "").TrimStart('\')
    
    $result = Fix-File $file
    
    switch ($result.Action) {
        "updated" {
            $stats.Fixed++
            $fixedFiles += @{
                Path = $relativePath
                Action = "✅ 更新目录"
            }
            Write-Host "✅ $relativePath - 更新目录" -ForegroundColor Green
        }
        "added" {
            $stats.Fixed++
            $fixedFiles += @{
                Path = $relativePath
                Action = "➕ 添加目录"
            }
            Write-Host "➕ $relativePath - 添加目录" -ForegroundColor Cyan
        }
        "skip" {
            $stats.Skipped++
            # Write-Host "⏭️  $relativePath - 跳过 ($($result.Reason))" -ForegroundColor Gray
        }
        "error" {
            $stats.Errors++
            Write-Host "❌ $relativePath - 错误: $($result.Reason)" -ForegroundColor Red
        }
    }
}

Write-Host ""
Write-Host "=" * 80
Write-Host "处理完成！"
Write-Host "=" * 80
Write-Host ""
Write-Host "总文件数: $($stats.Total)"
Write-Host "已修复: $($stats.Fixed)" -ForegroundColor Green
Write-Host "跳过: $($stats.Skipped)" -ForegroundColor Gray
Write-Host "错误: $($stats.Errors)" -ForegroundColor Red
Write-Host ""

if ($fixedFiles.Count -gt 0) {
    Write-Host "=" * 80
    Write-Host "已修复的文件:"
    Write-Host "=" * 80
    foreach ($item in $fixedFiles) {
        Write-Host "  $($item.Action) $($item.Path)"
    }
}

Write-Host ""
Write-Host "=" * 80

