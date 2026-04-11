# TypeScript 代码示例

本目录包含现代TypeScript编程的核心概念和最佳实践示例。

## 文件说明

### type_manipulation.ts

类型操作高级技巧，包括：

- 条件类型
- 映射类型
- 模板字面量类型
- 类型推断

### functional_utils.ts

函数式工具实现，包括：

- 高阶函数
- 函数组合
- 柯里化
- Monad模式

### async_patterns.ts

异步编程模式，包括：

- Promise模式
- Async/Await
- 异步迭代器
- 并发控制

## 运行要求

- TypeScript 4.5或更高版本（推荐5.0+）
- Node.js 16或更高版本

## 编译运行

```bash
# 安装TypeScript（如果尚未安装）
npm install -g typescript

# 编译
npx tsc --strict --target ES2020 --lib ES2020 type_manipulation.ts
npx tsc --strict --target ES2020 --lib ES2020 functional_utils.ts
npx tsc --strict --target ES2020 --lib ES2020 async_patterns.ts

# 运行
node type_manipulation.js
node functional_utils.js
node async_patterns.js
```

或使用ts-node直接运行：

```bash
npx ts-node type_manipulation.ts
```

## 学习建议

1. 先学习类型操作，理解TypeScript的类型系统
2. 掌握函数式编程工具，提高代码复用性
3. 精通异步模式，处理复杂异步场景
