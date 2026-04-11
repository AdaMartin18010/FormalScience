{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

-- | 类型类示例
-- 
-- 本文件展示 Haskell 的类型类系统：
-- - 基本类型类定义
-- - 类型类继承
-- - 多参数类型类
-- - 函数依赖
-- - 类型类等价于 Rust Trait / Java Interface
--
-- 对应理论：类型论、特设多态、约束多态

module Main where

import Data.List (sort)

-- ============================================================
-- 第一部分：基本类型类
-- ============================================================

{- |
类型类定义了一组类型共有的操作。
类似于数学中的"结构"概念。
-}

-- 可比较类型类（类似于 Ord）
class MyOrd a where
    myCompare :: a -> a -> Ordering
    myLessThan :: a -> a -> Bool
    myLessThan x y = myCompare x y == LT
    
    -- 默认实现
    myGreaterThan :: a -> a -> Bool
    myGreaterThan x y = myCompare x y == GT

-- 为 Int 实现 MyOrd
instance MyOrd Int where
    myCompare x y
        | x < y     = LT
        | x > y     = GT
        | otherwise = EQ

-- 为 [a] 实现（列表的字典序）
instance MyOrd a => MyOrd [a] where
    myCompare [] [] = EQ
    myCompare [] _  = LT
    myCompare _  [] = GT
    myCompare (x:xs) (y:ys) = 
        case myCompare x y of
            EQ -> myCompare xs ys
            other -> other

-- 使用示例
demoMyOrd :: IO ()
demoMyOrd = do
    putStrLn "=== MyOrd 类型类 ==="
    putStrLn $ "myCompare 3 5 = " ++ show (myCompare (3::Int) 5)
    putStrLn $ "myLessThan 3 5 = " ++ show (myLessThan (3::Int) (5::Int))
    putStrLn $ "myCompare [1,2] [1,3] = " ++ show (myCompare [1,2] [1,3::Int])
    putStrLn ""

-- ============================================================
-- 第二部分：类型类继承
-- ============================================================

{- |
类型类可以继承其他类型类，形成层次结构。
这对应于数学中结构的扩展（如群扩展为环）。
-}

-- 半群：有结合律的二元运算
class Semigroup a where
    (<>) :: a -> a -> a
    
    -- 结合律：x <> (y <> z) = (x <> y) <> z

-- 幺半群：有单位元的半群
class Semigroup a => Monoid a where
    mempty :: a
    
    -- 单位元律：mempty <> x = x <> mempty = x

-- 为列表实现
instance Semigroup [a] where
    (<>) = (++)

instance Monoid [a] where
    mempty = []

-- 为 Maybe 实现（使用 Monoid 约束）
instance Semigroup a => Semigroup (Maybe a) where
    Nothing <> my = my
    mx <> Nothing = mx
    Just x <> Just y = Just (x <> y)

instance Semigroup a => Monoid (Maybe a) where
    mempty = Nothing

demoMonoid :: IO ()
demoMonoid = do
    putStrLn "=== Monoid 类型类 ==="
    
    -- 列表幺半群
    putStrLn $ "[1,2] <> [3,4] = " ++ show ([1,2] <> [3,4::Int])
    putStrLn $ "mempty <> [1,2] = " ++ show (mempty <> [1,2::Int])
    
    -- Maybe 幺半群
    putStrLn $ "Just [1] <> Just [2] = " ++ show (Just [1] <> Just [2::Int])
    putStrLn $ "Just [1] <> Nothing = " ++ show (Just [1] <> (Nothing::Maybe [Int]))
    
    -- fold 操作
    putStrLn $ "fold [[1],[2],[3]] = " ++ show (fold [[1],[2],[3::Int]])
    
    putStrLn ""
    where fold = foldr (<>) mempty

-- ============================================================
-- 第三部分：数类型类层次
-- ============================================================

{- |
Haskell 的数值类型类形成精细的层次结构。
这允许精确控制哪些运算适用于哪些类型。
-}

-- 加法类型类
class Additive a where
    zero :: a
    add :: a -> a -> a

-- 乘法类型类
class Multiplicative a where
    one :: a
    mul :: a -> a -> a

-- 环：同时支持加法和乘法
class (Additive a, Multiplicative a) => Ring a where
    -- 分配律隐含在实例定义中

-- 域：支持除法的环
class Ring a => Field a where
    inv :: a -> Maybe a  -- 可能失败（除以零）

-- 实现：自然数（只有加法）
instance Additive Int where
    zero = 0
    add = (+)

-- 实现：有理数（域）
data Rational = Rational { numerator :: Int, denominator :: Int }
    deriving (Eq, Show)

instance Additive Rational where
    zero = Rational 0 1
    add (Rational n1 d1) (Rational n2 d2) = 
        Rational (n1 * d2 + n2 * d1) (d1 * d2)

instance Multiplicative Rational where
    one = Rational 1 1
    mul (Rational n1 d1) (Rational n2 d2) = 
        Rational (n1 * n2) (d1 * d2)

instance Ring Rational

instance Field Rational where
    inv (Rational 0 _) = Nothing
    inv (Rational n d) = Just (Rational d n)

demoNumeric :: IO ()
demoNumeric = do
    putStrLn "=== 数类型类 ==="
    
    putStrLn $ "add 3 5 = " ++ show (add (3::Int) 5)
    
    let r1 = Rational 1 2
    let r2 = Rational 1 3
    putStrLn $ "Rational 1/2 + 1/3 = " ++ show (add r1 r2)
    putStrLn $ "inv (Rational 2 3) = " ++ show (inv (Rational 2 3))
    putStrLn $ "inv (Rational 0 1) = " ++ show (inv (Rational 0 1))
    
    putStrLn ""

-- ============================================================
-- 第四部分：多参数类型类
-- ============================================================

{- |
多参数类型类允许表达类型之间的关系。
例如：集合类型与其元素类型的关系。
-}

-- 集合类型类
class Collection c e where
    empty :: c
    insert :: e -> c -> c
    member :: e -> c -> Bool
    toList :: c -> [e]

-- 列表作为集合（允许重复）
instance Eq a => Collection [a] a where
    empty = []
    insert = (:)
    member = elem
    toList = id

-- 自定义集合类型
data Set a = Set [a] deriving (Show)

instance Eq a => Collection (Set a) a where
    empty = Set []
    insert x (Set xs) 
        | x `elem` xs = Set xs
        | otherwise   = Set (x:xs)
    member x (Set xs) = x `elem` xs
    toList (Set xs) = xs

demoMultiParam :: IO ()
demoMultiParam = do
    putStrLn "=== 多参数类型类 ==="
    
    let list = insert 1 $ insert 2 $ insert 1 (empty :: [Int])
    putStrLn $ "List (with duplicates): " ++ show list
    putStrLn $ "Member 2: " ++ show (member (2::Int) list)
    
    let set = insert 1 $ insert 2 $ insert 1 (empty :: Set Int)
    putStrLn $ "Set (no duplicates): " ++ show set
    
    putStrLn ""

-- ============================================================
-- 第五部分：函数依赖
-- ============================================================

{- |
函数依赖允许表达类型参数之间的约束关系。
例如：容器类型决定元素类型，或反之。
-}

-- 带有函数依赖的类：e 由 c 决定
class CollectionFD c e | c -> e where
    emptyFD :: c
    insertFD :: e -> c -> c
    memberFD :: e -> c -> Bool

-- 现在一个集合类型只能有一个元素类型
instance CollectionFD [a] a where
    emptyFD = []
    insertFD = (:)
    memberFD = elem

-- 类型转换类型类
class Convertible a b | a -> b where
    convert :: a -> b

instance Convertible Int Double where
    convert = fromIntegral

instance Convertible Char Int where
    convert = fromEnum

-- 使用函数依赖进行类型推断
demoFunDeps :: IO ()
demoFunDeps = do
    putStrLn "=== 函数依赖 ==="
    
    -- 由于函数依赖 a -> b，类型推断器知道结果类型
    let x = convert (42::Int) :: Double
    putStrLn $ "convert 42 :: Int -> Double = " ++ show x
    
    let y = convert ('A'::Char) :: Int
    putStrLn $ "convert 'A' :: Char -> Int = " ++ show y
    
    putStrLn ""

-- ============================================================
-- 第六部分：高级类型类技巧
-- ============================================================

{- |
类型类可以提供默认实现，
子类只需实现最小所需的方法。
-}

-- 可枚举类型类
class Enum a where
    toEnum :: Int -> a
    fromEnum :: a -> Int
    
    -- 默认实现
    enumFrom :: a -> [a]
    enumFrom x = map toEnum [fromEnum x..]
    
    enumFromTo :: a -> a -> [a]
    enumFromTo x y = map toEnum [fromEnum x..fromEnum y]

-- 只为 Bool 实现最小接口
instance Enum Bool where
    toEnum 0 = False
    toEnum 1 = True
    toEnum _ = error "toEnum: out of bounds"
    
    fromEnum False = 0
    fromEnum True  = 1

-- 使用默认实现
demoDefaults :: IO ()
demoDefaults = do
    putStrLn "=== 默认实现 ==="
    putStrLn $ "enumFrom False = " ++ show (enumFrom False)
    putStrLn $ "enumFromTo False True = " ++ show (enumFromTo False True)
    putStrLn ""

-- ============================================================
-- 第七部分：类型类作为接口
-- ============================================================

{- |
类型类可以用来抽象接口，类似于面向对象中的接口。
-}

-- 可序列化类型类
class Serializable a where
    serialize :: a -> String
    deserialize :: String -> Maybe a

-- JSON-like 简单实现
instance Serializable Int where
    serialize = show
    deserialize s = case reads s of
        [(n, "")] -> Just n
        _         -> Nothing

instance Serializable a => Serializable [a] where
    serialize xs = "[" ++ concatMap ((++",") . serialize) (init xs) 
                        ++ serialize (last xs) ++ "]"
    deserialize ('[':']') = Just []
    deserialize s = undefined  -- 简化实现

-- 存储接口
class Storage s where
    save :: Serializable a => s -> String -> a -> IO ()
    load :: Serializable a => s -> String -> IO (Maybe a)

-- 内存存储实现
data MemoryStorage = MemoryStorage { store :: [(String, String)] }

instance Storage MemoryStorage where
    save st key value = putStrLn $ "Saving " ++ key ++ " = " ++ serialize value
    load st key = do
        putStrLn $ "Loading " ++ key
        return Nothing  -- 简化实现

demoInterfaces :: IO ()
demoInterfaces = do
    putStrLn "=== 类型类作为接口 ==="
    
    putStrLn $ "serialize 42 = " ++ serialize (42::Int)
    putStrLn $ "deserialize \"42\" :: Maybe Int = " ++ show (deserialize "42" :: Maybe Int)
    
    let memStore = MemoryStorage []
    save memStore "counter" (100::Int)
    
    putStrLn ""

-- ============================================================
-- 第八部分：类型类与类型安全
-- ============================================================

{- |
类型类提供编译时多态，保证类型安全。
-}

-- 安全的钱类型
newtype Money = Money { unMoney :: Rational }
    deriving (Eq, Show)

newtype Percentage = Percentage { unPercentage :: Rational }
    deriving (Eq, Show)

-- 禁止直接相加不同类型的值
-- Money 1 + Percentage 10  -- 类型错误！

-- 但有意义的操作是允许的
applyDiscount :: Money -> Percentage -> Money
applyDiscount (Money m) (Percentage p) = 
    Money (m * (1 - p / 100))

addMoney :: Money -> Money -> Money
addMoney (Money m1) (Money m2) = Money (m1 + m2)

demoTypeSafety :: IO ()
demoTypeSafety = do
    putStrLn "=== 类型安全 ==="
    
    let price = Money 100
    let discount = Percentage 10
    
    putStrLn $ "Price: " ++ show price
    putStrLn $ "Discount: " ++ show discount
    putStrLn $ "After discount: " ++ show (applyDiscount price discount)
    
    -- 编译时防止错误：
    -- putStrLn $ "Invalid: " ++ show (price + discount)  -- 类型错误！
    
    putStrLn ""

-- ============================================================
-- 总结
-- ============================================================

main :: IO ()
main = do
    putStrLn "╔══════════════════════════════════════════════════════════╗"
    putStrLn "║          Haskell 类型类示例                              ║"
    putStrLn "╚══════════════════════════════════════════════════════════╝"
    putStrLn ""
    
    demoMyOrd
    demoMonoid
    demoNumeric
    demoMultiParam
    demoFunDeps
    demoDefaults
    demoInterfaces
    demoTypeSafety
    
    putStrLn "╔══════════════════════════════════════════════════════════╗"
    putStrLn "║          所有示例运行完成！                               ║"
    putStrLn "╚══════════════════════════════════════════════════════════╝"

{- 输出说明：

编译和运行：
```bash
ghc --make type_class.hs -o type_class
./type_class
```

或使用 runhaskell：
```bash
runhaskell type_class.hs
```

预期输出：
```
╔══════════════════════════════════════════════════════════╗
║          Haskell 类型类示例                              ║
╚══════════════════════════════════════════════════════════╝

=== MyOrd 类型类 ===
myCompare 3 5 = LT
...

╔══════════════════════════════════════════════════════════╗
║          所有示例运行完成！                               ║
╚══════════════════════════════════════════════════════════╝
```

理论对应：
- 类型类 ↔ 逻辑中的谓词 / 结构中的公理
- 类型类实例 ↔ 结构实现 / 证明
- 多参数类型类 ↔ 关系
- 函数依赖 ↔ 函数关系
- 默认实现 ↔ 推导定理

Haskell 类型类提供了：
- 编译时特设多态
- 类型安全的代码重用
- 清晰的接口抽象
- 与数学结构的直接对应
-}
