# 验证本地链接完整性脚本
# 2025-10-29

param(
    [string]$TargetPath = "Software_Perspective",
    [string]$OutputFile = "BROKEN_LINKS_RESULTS.md"
)

$basePath = "e:\_src\FormalScience\Concept"
$targetFullPath = Join-Path $basePath $TargetPath
$brokenLinks = @()
$validLinks = @()
$totalLinks = 0

Write-Host "🔍 开始验证: $TargetPath" -ForegroundColor Cyan
Write-Host ""

Get-ChildItem -Path $targetFullPath -Recurse -Filter "*.md" | ForEach-Object {
    $file = $_
    $relativePath = $file.FullName.Replace("$basePath\", "")
    Write-Host "  检查: $relativePath" -NoNewline
    
    $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
    if (-not $content) {
        Write-Host " [空文件]" -ForegroundColor Yellow
        return
    }
    
    # 提取所有本地链接 (./xxx.md 和 ../xxx.md)
    $links = [regex]::Matches($content, '\]\((\.\.?/[^)]+\.md)\)')
    
    $fileLinksCount = 0
    $fileBrokenCount = 0
    
    foreach ($link in $links) {
        $totalLinks++
        $fileLinksCount++
        $linkPath = $link.Groups[1].Value
        
        # 构建完整路径
        $linkDir = Split-Path $file.FullName
        $fullPath = Join-Path $linkDir $linkPath
        
        try {
            $resolvedPath = [System.IO.Path]::GetFullPath($fullPath)
            
            if (Test-Path $resolvedPath) {
                $validLinks += [PSCustomObject]@{
                    File = $relativePath
                    Link = $linkPath
                    Target = $resolvedPath.Replace("$basePath\", "")
                    Status = "✓"
                }
            } else {
                $fileBrokenCount++
                $brokenLinks += [PSCustomObject]@{
                    File = $relativePath
                    Link = $linkPath
                    Target = $resolvedPath.Replace("$basePath\", "")
                    Status = "✗"
                }
            }
        } catch {
            $fileBrokenCount++
            $brokenLinks += [PSCustomObject]@{
                File = $relativePath
                Link = $linkPath
                Target = "无法解析"
                Status = "✗"
            }
        }
    }
    
    if ($fileLinksCount -eq 0) {
        Write-Host " [无链接]" -ForegroundColor Gray
    } elseif ($fileBrokenCount -eq 0) {
        Write-Host " ✓ $fileLinksCount 链接有效" -ForegroundColor Green
    } else {
        Write-Host " ✗ $fileBrokenCount/$fileLinksCount 断链" -ForegroundColor Red
    }
}

Write-Host ""
Write-Host "================================================================" -ForegroundColor Cyan
Write-Host "  验证完成" -ForegroundColor Green
Write-Host "================================================================" -ForegroundColor Cyan
Write-Host ""
Write-Host "  总链接数: $totalLinks"
Write-Host "  有效链接: $($validLinks.Count) ($('{0:P0}' -f ($validLinks.Count / $totalLinks)))"
Write-Host "  断链数:   $($brokenLinks.Count) ($('{0:P0}' -f ($brokenLinks.Count / $totalLinks)))"
Write-Host ""

# 生成Markdown报告
$report = @"
# 🔍 $TargetPath - 本地链接验证报告

**验证时间**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")  
**验证范围**: $TargetPath  
**总链接数**: $totalLinks  
**有效链接**: $($validLinks.Count)  
**断链数**: $($brokenLinks.Count)  
**断链率**: $('{0:P1}' -f ($brokenLinks.Count / $totalLinks))

---

## ❌ 断链列表 ($($brokenLinks.Count)个)

"@

if ($brokenLinks.Count -gt 0) {
    # 按文件分组
    $brokenByFile = $brokenLinks | Group-Object File
    
    foreach ($fileGroup in $brokenByFile) {
        $report += @"

### $($fileGroup.Name)
**断链数**: $($fileGroup.Count)

"@
        foreach ($link in $fileGroup.Group) {
            $report += "- ❌ ``$($link.Link)``  `n"
            $report += "  - 目标: ``$($link.Target)``  `n"
        }
    }
} else {
    $report += "`n🎉 **没有发现断链！所有链接均有效！**`n"
}

$report += @"

---

## ✅ 链接统计

| 指标 | 数量 | 百分比 |
|------|------|--------|
| 总链接数 | $totalLinks | 100% |
| 有效链接 | $($validLinks.Count) | $('{0:P1}' -f ($validLinks.Count / $totalLinks)) |
| 断链数 | $($brokenLinks.Count) | $('{0:P1}' -f ($brokenLinks.Count / $totalLinks)) |

---

**生成时间**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")
"@

# 保存报告
$reportPath = Join-Path $basePath $OutputFile
$report | Out-File -FilePath $reportPath -Encoding UTF8
Write-Host "📄 报告已生成: $OutputFile" -ForegroundColor Green
Write-Host ""

# 返回结果
return [PSCustomObject]@{
    TotalLinks = $totalLinks
    ValidLinks = $validLinks.Count
    BrokenLinks = $brokenLinks.Count
    BrokenRate = ($brokenLinks.Count / $totalLinks)
}

