/**
 * Markdown 目录修复核心库 - v2.0
 */

const fs = require('fs');
const path = require('path');

class TOCFixerV2 {
  constructor(baseDir) {
    this.baseDir = baseDir;
    this.stats = { total: 0, fixed: 0, skipped: 0, errors: 0 };
    this.fixedFiles = [];
  }

  // 生成 GitHub 风格的 anchor
  generateAnchor(text) {
    return text
      .toLowerCase()
      .replace(/[^\w\s\u4e00-\u9fff_-]/g, '')
      .replace(/\s+/g, '-')
      .replace(/_/g, '-')
      // .replace(/-+/g, '-')  // ❌ 移除：GitHub保留多个连续的-
      .replace(/^-+|-+$/g, '');  // ✅ 只移除开头和结尾的-
  }

  // 提取标题（跳过 <details> 块内的内容）
  extractHeadings(content) {
    // 统一处理换行符（Windows \r\n 和 Unix \n）
    const lines = content.replace(/\r\n/g, '\n').split('\n');
    const headings = [];
    let inCodeBlock = false;
    let inDetailsBlock = false;
    let detailsDepth = 0;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      const trimmed = line.trim();

      // 检测代码块
      if (trimmed.startsWith('```')) {
        inCodeBlock = !inCodeBlock;
        continue;
      }
      if (inCodeBlock) continue;

      // 检测 <details> 块的开始和结束
      if (trimmed.startsWith('<details>')) {
        inDetailsBlock = true;
        detailsDepth++;
        continue;
      }
      if (trimmed.startsWith('</details>')) {
        detailsDepth--;
        if (detailsDepth <= 0) {
          inDetailsBlock = false;
          detailsDepth = 0;
        }
        continue;
      }

      // 跳过 <details> 块内的所有内容（包括标题）
      if (inDetailsBlock) continue;

      // 提取标题
      const match = line.match(/^(#{1,6})\s+(.+)$/);
      if (match) {
        const level = match[1].length;
        const text = match[2].trim();
        const anchor = this.generateAnchor(text);
        
        headings.push({ 
          level, 
          text, 
          anchor,
          lineNumber: i + 1 
        });
      }
    }

    return headings;
  }

  // 生成目录
  generateTOC(headings) {
    if (headings.length === 0) return '';

    const lines = ['## 📋 目录', ''];

    // 跳过第一个标题（文件标题）
    let startIdx = 1;
    
    // 如果第二个标题是"目录"相关，也跳过
    if (headings.length > 1) {
      const secondTitle = headings[1].text.toLowerCase();
      if (secondTitle.includes('目录') || 
          secondTitle.includes('table of contents') ||
          secondTitle.includes('toc')) {
        startIdx = 2;
      }
    }

    for (let i = startIdx; i < headings.length; i++) {
      const { level, text, anchor } = headings[i];
      
      // 只包含 2-4 级标题
      if (level < 2 || level > 4) continue;

      const indent = '  '.repeat(level - 2);
      lines.push(`${indent}- [${text}](#${anchor})`);
    }

    lines.push('');
    return lines.join('\n');
  }

  // 查找现有目录位置
  findTOCSection(content) {
    // 统一处理换行符
    const lines = content.replace(/\r\n/g, '\n').split('\n');
    
    const patterns = [
      /^\s*##\s*📋\s*目录/,
      /^\s*##\s*目录/,
      /^\s*##\s*Table of Contents/i,
      /^\s*##\s*📖\s*目录/
    ];

    let startLine = -1;
    
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      for (const pattern of patterns) {
        if (pattern.test(line)) {
          startLine = i;
          break;
        }
      }
      if (startLine >= 0) break;
    }

    if (startLine === -1) return { lines: null, start: -1, end: -1 };

    // 查找结束位置（下一个 ## 标题或 --- 分隔符）
    let endLine = startLine + 1;
    for (let i = startLine + 1; i < lines.length; i++) {
      const line = lines[i].trim();
      
      // 遇到下一个 ## 标题
      if (/^##\s+[^#]/.test(line)) {
        endLine = i;
        break;
      }
      
      // 遇到分隔符（且不是紧跟目录标题的那个）
      if (line === '---' && i > startLine + 2) {
        endLine = i;
        break;
      }
    }

    return { lines, start: startLine, end: endLine };
  }

  // 修复单个文件
  fixFile(filepath) {
    try {
      const content = fs.readFileSync(filepath, 'utf8');
      // 统一处理换行符
      const lines = content.replace(/\r\n/g, '\n').split('\n');

      // 提取标题（跳过 <details> 块）
      const headings = this.extractHeadings(content);

      if (headings.length < 3) {
        return { action: 'skip', reason: 'too few headings' };
      }

      // 生成新目录
      const newTOC = this.generateTOC(headings);
      if (!newTOC) {
        return { action: 'skip', reason: 'no valid headings' };
      }

      // 查找现有目录
      const tocSection = this.findTOCSection(content);

      let newLines;
      let action;

      if (tocSection && tocSection.lines) {
        const lines = tocSection.lines;
        // 更新现有目录
        newLines = [
          ...lines.slice(0, tocSection.start),
          ...newTOC.split('\n'),
          ...lines.slice(tocSection.end)
        ];
        action = 'updated';
      } else {
        // 查找插入位置
        let insertPos = 0;
        let inMetadata = false;
        let inDetailsBlock = false;

        for (let i = 0; i < lines.length; i++) {
          const line = lines[i];
          const trimmed = line.trim();
          
          // 检测元数据块
          if (i === 0 && trimmed.startsWith('>')) {
            inMetadata = true;
          }

          if (inMetadata) {
            if (trimmed === '---') {
              insertPos = i + 1;
              break;
            }
            if (!trimmed.startsWith('>') && trimmed !== '') {
              inMetadata = false;
            }
          }

          // 跳过 <details> 块
          if (trimmed.startsWith('<details>')) {
            inDetailsBlock = true;
          }
          if (trimmed.startsWith('</details>')) {
            inDetailsBlock = false;
            insertPos = i + 1;
            continue;
          }
          if (inDetailsBlock) continue;

          // 找到第一个 ## 标题（非目录标题）
          if (/^##\s+/.test(line) && 
              !trimmed.includes('目录') && 
              !trimmed.toLowerCase().includes('table of contents')) {
            insertPos = i;
            break;
          }
        }

        // 插入新目录
        newLines = [
          ...lines.slice(0, insertPos),
          '',
          '---',
          '',
          ...newTOC.split('\n'),
          '',
          '---',
          '',
          ...lines.slice(insertPos)
        ];
        action = 'added';
      }

      // 写回文件
      const newContent = newLines.join('\n');
      
      // 只有内容真正改变时才写入
      if (newContent !== content.replace(/\r\n/g, '\n')) {
        fs.writeFileSync(filepath, newContent, 'utf8');
        return { action, reason: `TOC ${action}`, headings: headings.length };
      } else {
        return { action: 'skip', reason: 'no changes needed' };
      }
    } catch (error) {
      return { action: 'error', reason: error.message };
    }
  }

  // 递归扫描目录
  scanDirectory(dir) {
    const items = fs.readdirSync(dir);

    for (const item of items) {
      const fullPath = path.join(dir, item);
      const stat = fs.statSync(fullPath);

      if (stat.isDirectory()) {
        if (['node_modules', '.git', 'venv'].includes(item)) continue;
        this.scanDirectory(fullPath);
      } else if (item.endsWith('.md')) {
        this.processFile(fullPath);
      }
    }
  }

  // 处理单个文件
  processFile(filepath) {
    this.stats.total++;
    
    const relativePath = path.relative(this.baseDir, filepath);
    const result = this.fixFile(filepath);

    switch (result.action) {
      case 'updated':
        this.stats.fixed++;
        this.fixedFiles.push({ 
          path: relativePath, 
          action: '✅ 更新目录',
          headings: result.headings 
        });
        console.log(`✅ ${relativePath} - 更新目录 (${result.headings} 个标题)`);
        break;
      case 'added':
        this.stats.fixed++;
        this.fixedFiles.push({ 
          path: relativePath, 
          action: '➕ 添加目录',
          headings: result.headings 
        });
        console.log(`➕ ${relativePath} - 添加目录 (${result.headings} 个标题)`);
        break;
      case 'skip':
        this.stats.skipped++;
        // console.log(`⏭️  ${relativePath} - ${result.reason}`);
        break;
      case 'error':
        this.stats.errors++;
        console.log(`❌ ${relativePath} - 错误: ${result.reason}`);
        break;
    }
  }

  printSummary() {
    console.log('');
    console.log('='.repeat(80));
    console.log('处理完成！');
    console.log('='.repeat(80));
    console.log('');
    console.log(`总文件数: ${this.stats.total}`);
    console.log(`已修复: ${this.stats.fixed}`);
    console.log(`跳过: ${this.stats.skipped}`);
    console.log(`错误: ${this.stats.errors}`);
    console.log('');

    if (this.fixedFiles.length > 0) {
      console.log('='.repeat(80));
      console.log('已修复的文件:');
      console.log('='.repeat(80));
      this.fixedFiles.slice(0, 30).forEach(item => {
        console.log(`  ${item.action} ${item.path} (${item.headings} 个标题)`);
      });
      if (this.fixedFiles.length > 30) {
        console.log(`  ... 还有 ${this.fixedFiles.length - 30} 个文件`);
      }
    }
  }
}

module.exports = TOCFixerV2;

