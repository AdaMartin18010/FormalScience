#!/usr/bin/env node
/**
 * 修复 Markdown 文件的目录 - v2.0
 * 正确处理：
 * 1. 跳过 <details> 折叠块内的标题
 * 2. 只提取正文中的标题
 * 3. 移除重复的自引用
 */

const TOCFixerV2 = require('./fix-toc-v2-lib.js');

// 主程序
const baseDir = __dirname;
const fixer = new TOCFixerV2(baseDir);

// 检查命令行参数
const args = process.argv.slice(2);

if (args.includes('--test')) {
  // 测试模式：只处理几个示例文件
  console.log('='.repeat(80));
  console.log('Markdown 目录修复工具 v2.0 - 测试模式');
  console.log('='.repeat(80));
  console.log('');
  
  const testFiles = [
    'AI_model_Perspective/03_Language_Models/03.2_Neural_Language_Models.md',
    'FormalLanguage_Perspective/01_Philosophical_Foundations/01.4_Meaning_Construction_Process.md',
    'Information_Theory_Perspective/01_Complexity_Analysis/01.1_Time_Complexity.md'
  ];
  
  console.log('⚠️  只处理测试文件:');
  testFiles.forEach(f => console.log(`  - ${f}`));
  console.log('');

  testFiles.forEach(file => {
    const path = require('path');
    const fullPath = path.join(baseDir, file);
    const fs = require('fs');
    if (fs.existsSync(fullPath)) {
      fixer.processFile(fullPath);
    } else {
      console.log(`❌ 文件不存在: ${file}`);
    }
  });

  fixer.printSummary();
  
} else if (args.includes('--help')) {
  console.log(`
用法: node fix-toc-v2.js [选项]

选项:
  --test    测试模式（只处理3个示例文件）
  --help    显示帮助信息
  (无参数)  全量模式（处理所有文件）

示例:
  node fix-toc-v2.js --test    # 先测试
  node fix-toc-v2.js           # 全量处理
`);
} else {
  // 全量模式
  console.log('='.repeat(80));
  console.log('Markdown 目录修复工具 v2.0');
  console.log('='.repeat(80));
  console.log('');
  console.log('✨ v2.0 改进:');
  console.log('  - ✅ 正确跳过 <details> 折叠块内的标题');
  console.log('  - ✅ 只提取正文中的标题');
  console.log('  - ✅ 移除重复的自引用');
  console.log('');

  fixer.scanDirectory(baseDir);
  fixer.printSummary();
}
