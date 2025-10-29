#!/usr/bin/env node
/**
 * 修复 Markdown 文件的目录
 * Usage: node fix-toc.js
 */

const fs = require('fs');
const path = require('path');

class TOCFixer {
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
      .replace(/-+/g, '-')
      .replace(/^-|-$/g, '');
  }

  // 提取标题
  extractHeadings(content) {
    const lines = content.split('\n');
    const headings = [];
    let inCodeBlock = false;

    for (const line of lines) {
      if (line.trim().startsWith('```')) {
        inCodeBlock = !inCodeBlock;
        continue;
      }
      if (inCodeBlock) continue;

      const match = line.match(/^(#{1,6})\s+(.+)$/);
      if (match) {
        const level = match[1].length;
        const text = match[2].trim();
        const anchor = this.generateAnchor(text);
        headings.push({ level, text, anchor });
      }
    }

    return headings;
  }

  // 生成目录
  generateTOC(headings) {
    if (headings.length === 0) return '';

    const lines = ['## 📋 目录', ''];

    // 跳过第一个标题（文件标题）
    for (let i = 1; i < headings.length; i++) {
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
  findTOCSection(lines) {
    const patterns = [
      /^\s*##\s*📋\s*目录/,
      /^\s*##\s*目录/,
      /^\s*##\s*Table of Contents/i,
      /^\s*##\s*📖\s*目录/
    ];

    let startLine = -1;
    for (let i = 0; i < lines.length; i++) {
      if (patterns.some(p => p.test(lines[i]))) {
        startLine = i;
        break;
      }
    }

    if (startLine === -1) return null;

    // 查找结束位置
    let endLine = startLine + 1;
    for (let i = startLine + 1; i < lines.length; i++) {
      const line = lines[i].trim();
      if (/^##\s+[^#]/.test(line) || (line === '---' && i > startLine + 2)) {
        endLine = i;
        break;
      }
    }

    return { start: startLine, end: endLine };
  }

  // 修复单个文件
  fixFile(filepath) {
    try {
      const content = fs.readFileSync(filepath, 'utf8');
      const lines = content.split('\n');

      // 提取标题
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
      const tocSection = this.findTOCSection(lines);

      let newLines;
      let action;

      if (tocSection) {
        // 更新现有目录
        newLines = [
          ...lines.slice(0, tocSection.start),
          ...newTOC.split('\n'),
          ...lines.slice(tocSection.end)
        ];
        action = 'updated';
      } else {
        // 查找插入位置（元数据块之后）
        let insertPos = 0;
        let inMetadata = false;

        for (let i = 0; i < lines.length; i++) {
          const line = lines[i];
          
          if (i === 0 && line.trim().startsWith('>')) {
            inMetadata = true;
          }

          if (inMetadata) {
            if (line.trim() === '---') {
              insertPos = i + 1;
              break;
            }
            if (!line.trim().startsWith('>') && line.trim() !== '') {
              inMetadata = false;
            }
          }

          if (/^##\s+/.test(line)) {
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
      fs.writeFileSync(filepath, newContent, 'utf8');

      return { action, reason: `TOC ${action}` };
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

      // 跳过特殊目录
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
        this.fixedFiles.push({ path: relativePath, action: '✅ 更新目录' });
        console.log(`✅ ${relativePath} - 更新目录`);
        break;
      case 'added':
        this.stats.fixed++;
        this.fixedFiles.push({ path: relativePath, action: '➕ 添加目录' });
        console.log(`➕ ${relativePath} - 添加目录`);
        break;
      case 'skip':
        this.stats.skipped++;
        break;
      case 'error':
        this.stats.errors++;
        console.log(`❌ ${relativePath} - 错误: ${result.reason}`);
        break;
    }
  }

  // 运行
  run() {
    console.log('='.repeat(80));
    console.log('Markdown 目录修复工具');
    console.log('='.repeat(80));
    console.log('');

    this.scanDirectory(this.baseDir);

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
      this.fixedFiles.slice(0, 50).forEach(item => {
        console.log(`  ${item.action} ${item.path}`);
      });
      if (this.fixedFiles.length > 50) {
        console.log(`  ... 还有 ${this.fixedFiles.length - 50} 个文件`);
      }
    }
  }
}

// 运行
const baseDir = __dirname;
const fixer = new TOCFixer(baseDir);
fixer.run();

