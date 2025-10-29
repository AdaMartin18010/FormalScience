#!/usr/bin/env node
/**
 * 分批处理 Markdown 目录修复
 * 按视角目录逐个处理，方便查看和控制
 */

const fs = require('fs');
const path = require('path');

// 导入主修复类
const TOCFixerV2 = require('./fix-toc-v2-lib.js');

const baseDir = __dirname;

const perspectives = [
  { name: 'AI_model_Perspective', desc: 'AI模型视角' },
  { name: 'FormalLanguage_Perspective', desc: '形式语言视角' },
  { name: 'Information_Theory_Perspective', desc: '信息论视角' },
  { name: 'Program_Algorithm_Perspective', desc: '程序算法视角' },
  { name: 'Software_Perspective', desc: '软件视角' }
];

async function promptUser(question) {
  const readline = require('readline');
  const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout
  });

  return new Promise((resolve) => {
    rl.question(question, (answer) => {
      rl.close();
      resolve(answer.trim().toLowerCase());
    });
  });
}

async function processBatch(perspectiveName, description) {
  console.log('');
  console.log('='.repeat(80));
  console.log(`处理: ${description} (${perspectiveName})`);
  console.log('='.repeat(80));
  console.log('');

  const targetDir = path.join(baseDir, perspectiveName);
  
  if (!fs.existsSync(targetDir)) {
    console.log(`⚠️  目录不存在: ${targetDir}`);
    return { processed: 0, fixed: 0, skipped: 0, errors: 0 };
  }

  const fixer = new TOCFixerV2(targetDir);
  fixer.scanDirectory(targetDir);
  
  console.log('');
  console.log(`✅ 处理完成: ${fixer.stats.total} 个文件`);
  console.log(`   - 已修复: ${fixer.stats.fixed}`);
  console.log(`   - 跳过: ${fixer.stats.skipped}`);
  console.log(`   - 错误: ${fixer.stats.errors}`);

  return fixer.stats;
}

async function main() {
  console.log('');
  console.log('╔' + '═'.repeat(78) + '╗');
  console.log('║' + ' '.repeat(20) + 'Markdown 目录修复 - 分批处理模式' + ' '.repeat(23) + '║');
  console.log('╚' + '═'.repeat(78) + '╝');
  console.log('');
  console.log('总共 5 个视角目录:');
  perspectives.forEach((p, i) => {
    const count = countMarkdownFiles(path.join(baseDir, p.name));
    console.log(`  ${i + 1}. ${p.desc} (${p.name}): ${count} 个文件`);
  });
  console.log('');

  const totalStats = { total: 0, fixed: 0, skipped: 0, errors: 0 };

  for (let i = 0; i < perspectives.length; i++) {
    const { name, desc } = perspectives[i];
    
    console.log(`\n[${i + 1}/${perspectives.length}] 准备处理: ${desc}`);
    console.log('选项: [y]处理 [s]跳过 [q]退出');
    
    const answer = await promptUser('您的选择 (y/s/q): ');
    
    if (answer === 'q') {
      console.log('\n⏹️  用户终止处理');
      break;
    } else if (answer === 's') {
      console.log(`⏭️  跳过: ${desc}`);
      continue;
    }
    
    const stats = await processBatch(name, desc);
    totalStats.total += stats.total;
    totalStats.fixed += stats.fixed;
    totalStats.skipped += stats.skipped;
    totalStats.errors += stats.errors;
  }

  console.log('');
  console.log('='.repeat(80));
  console.log('全部处理完成！');
  console.log('='.repeat(80));
  console.log('');
  console.log(`总文件数: ${totalStats.total}`);
  console.log(`已修复: ${totalStats.fixed}`);
  console.log(`跳过: ${totalStats.skipped}`);
  console.log(`错误: ${totalStats.errors}`);
  console.log('');
}

function countMarkdownFiles(dir) {
  if (!fs.existsSync(dir)) return 0;
  
  let count = 0;
  const items = fs.readdirSync(dir);
  
  for (const item of items) {
    const fullPath = path.join(dir, item);
    const stat = fs.statSync(fullPath);
    
    if (stat.isDirectory()) {
      if (['node_modules', '.git'].includes(item)) continue;
      count += countMarkdownFiles(fullPath);
    } else if (item.endsWith('.md')) {
      count++;
    }
  }
  
  return count;
}

// 检查是否为非交互式模式
const args = process.argv.slice(2);
if (args.includes('--auto')) {
  console.log('⚠️  自动模式：将处理所有视角，无需确认');
  console.log('');
  
  (async () => {
    const totalStats = { total: 0, fixed: 0, skipped: 0, errors: 0 };
    
    for (const { name, desc } of perspectives) {
      const stats = await processBatch(name, desc);
      totalStats.total += stats.total;
      totalStats.fixed += stats.fixed;
      totalStats.skipped += stats.skipped;
      totalStats.errors += stats.errors;
    }
    
    console.log('');
    console.log('='.repeat(80));
    console.log('全部处理完成！');
    console.log('='.repeat(80));
    console.log('');
    console.log(`总文件数: ${totalStats.total}`);
    console.log(`已修复: ${totalStats.fixed}`);
    console.log(`跳过: ${totalStats.skipped}`);
    console.log(`错误: ${totalStats.errors}`);
  })();
} else {
  main().catch(console.error);
}

