// 为markdown文档生成目录的Node.js脚本
const fs = require('fs');
const path = require('path');

function extractHeadings(content) {
    const lines = content.split('\n');
    const headings = [];
    
    for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        const match = line.match(/^(#{2,6})\s+(.+)$/);
        if (match) {
            const level = match[1].length;
            const title = match[2];
            headings.push({ level, title, line: i + 1 });
        }
    }
    
    return headings;
}

function generateTOC(headings) {
    const toc = ['## 目录 | Table of Contents', ''];
    
    for (const heading of headings) {
        const indent = '  '.repeat(heading.level - 2);
        // 生成anchor链接
        const anchor = heading.title
            .toLowerCase()
            .replace(/\s+/g, '-')
            .replace(/[^\w\u4e00-\u9fa5-]/g, '');
        
        toc.push(`${indent}- [${heading.title}](#${anchor})`);
    }
    
    toc.push('');
    toc.push('---');
    toc.push('');
    
    return toc.join('\n');
}

function addTOCtoFile(filePath) {
    const content = fs.readFileSync(filePath, 'utf8');
    
    // 检查是否已有目录
    if (content.includes('## 目录') || content.includes('## Table of Contents')) {
        console.log(`跳过（已有目录）: ${filePath}`);
        return false;
    }
    
    const lines = content.split('\n');
    const headings = extractHeadings(content);
    
    if (headings.length === 0) {
        console.log(`跳过（无标题）: ${filePath}`);
        return false;
    }
    
    // 找到第一个二级标题的位置
    let insertPos = -1;
    for (let i = 0; i < lines.length; i++) {
        if (lines[i].match(/^##\s+/)) {
            insertPos = i;
            break;
        }
    }
    
    if (insertPos === -1) {
        console.log(`跳过（格式异常）: ${filePath}`);
        return false;
    }
    
    // 生成目录
    const toc = generateTOC(headings);
    
    // 插入目录
    lines.splice(insertPos, 0, toc);
    
    // 写回文件
    fs.writeFileSync(filePath, lines.join('\n'), 'utf8');
    console.log(`✓ 已添加目录: ${filePath}`);
    return true;
}

// 主函数
function main() {
    const dir = process.argv[2] || '.';
    console.log(`扫描目录: ${dir}`);
    
    // 递归处理
    function processDir(dirPath) {
        const files = fs.readdirSync(dirPath);
        
        for (const file of files) {
            const filePath = path.join(dirPath, file);
            const stat = fs.statSync(filePath);
            
            if (stat.isDirectory()) {
                // 跳过某些目录
                if (file.startsWith('.') || file === 'node_modules') {
                    continue;
                }
                processDir(filePath);
            } else if (file.endsWith('.md')) {
                // 跳过报告和临时文件
                if (file.includes('REPORT') || file.includes('SUMMARY') || 
                    file.includes('README') || file.includes('INDEX') ||
                    file === 'generate_toc.js' || file === 'analyze_docs.py') {
                    continue;
                }
                
                addTOCtoFile(filePath);
            }
        }
    }
    
    processDir(dir);
}

if (require.main === module) {
    main();
}

