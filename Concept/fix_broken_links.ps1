# 智能修复断链脚本
# 策略: 删除断链行，保留有效链接

param(
    [string]$FilePath,
    [string[]]$BrokenLinks
)

Write-Host "🔧 修复文件: $FilePath" -ForegroundColor Cyan
Write-Host "📋 断链数: $($BrokenLinks.Count)" -ForegroundColor Yellow

$content = Get-Content $FilePath -Raw -Encoding UTF8

$originalLineCount = ($content -split "`n").Count
$fixedCount = 0

foreach ($link in $BrokenLinks) {
    # 转义特殊正则字符
    $escapedLink = [regex]::Escape($link)
    
    # 匹配整行 (Markdown列表项)
    $pattern = "(?m)^.*\($escapedLink\).*`r?`n"
    
    if ($content -match $pattern) {
        $content = $content -replace $pattern, ""
        $fixedCount++
        Write-Host "  ✓ 删除: $link" -ForegroundColor Green
    }
}

# 保存修复后的文件
$content | Out-File -FilePath $FilePath -Encoding UTF8 -NoNewline

$newLineCount = ($content -split "`n").Count
Write-Host ""
Write-Host "✅ 修复完成:" -ForegroundColor Green
Write-Host "  原始行数: $originalLineCount"
Write-Host "  修复后行数: $newLineCount"
Write-Host "  删除行数: $($originalLineCount - $newLineCount)"
Write-Host "  处理断链: $fixedCount / $($BrokenLinks.Count)"
Write-Host ""

