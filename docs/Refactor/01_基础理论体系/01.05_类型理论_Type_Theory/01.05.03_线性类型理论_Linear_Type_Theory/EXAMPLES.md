# 04.3 线性/仿射类型 极简示例

## 📋 目录

- [04.3 线性/仿射类型 极简示例](#043-线性仿射类型-极简示例)
  - [📋 目录](#-目录)
  - [1 Haskell LinearTypesGHC -XLinearTypes](#1-haskell-lineartypesghc--xlineartypes)
  - [2 Lean非线性示意，资源由类型刻画](#2-lean非线性示意资源由类型刻画)

---

## 1 Haskell LinearTypesGHC -XLinearTypes

```haskell
{-# LANGUAGE LinearTypes #-}

module LinearExample where

-- 线性函数: 参数 x 必须恰好使用一次
linId :: a %1 -> a
linId x = x

-- 线性对的拆分
linSwap :: (a, b) %1 -> (b, a)
linSwap (x, y) = (y, x)
```

编译：`ghc -XLinearTypes LinearExample.hs`

## 2 Lean非线性示意，资源由类型刻画

```lean
-- 以长度为索引的向量，保证 map 保持长度

def mapVec {α β : Type} {n : Nat}
  (f : α → β) : Vector α n → Vector β n :=
λ v => Vector.map f v
```

说明：Lean 本体非线性；线性/仿射语义可通过外部逻辑/约束模拟或以 Rust 展示工程实现。
