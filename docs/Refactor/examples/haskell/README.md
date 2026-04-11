# Haskell 函数式编程示例库

本目录包含使用 Haskell 编写的示例，展示 Haskell 的类型系统和函数式编程特性。

## 文件说明

| 文件 | 内容 | 对应理论 |
|------|------|----------|
| `functor_monad.hs` | 函子、应用函子、单子 | 范畴论、单子论 |
| `type_class.hs` | 类型类和多态 | 类型论、特设多态 |

## 运行要求

- GHC (Glasgow Haskell Compiler) ≥ 9.0
- Cabal 或 Stack 构建工具

## 编译与运行

```bash
# 直接使用 GHC 编译
ghc --make functor_monad.hs -o functor_monad
./functor_monad

# 或使用 runhaskell 直接运行
runhaskell functor_monad.hs

# 使用 Cabal
cabal init
cabal build
cabal run
```

## 学习路径

1. **基础**: 从 `functor_monad.hs` 开始，理解 Haskell 的核心抽象
2. **进阶**: 阅读 `type_class.hs`，掌握类型类系统

## 相关资源

- [Learn You a Haskell](http://learnyouahaskell.com/)
- [Real World Haskell](http://book.realworldhaskell.org/)
- [Haskell Wiki](https://wiki.haskell.org/)
