{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}

-- | 函子和单子示例
-- 
-- 本文件展示 Haskell 中函子、应用函子和单子的实现和应用：
-- - Functor（函子）：可映射的上下文
-- - Applicative（应用函子）：带上下文的函数应用
-- - Monad（单子）：可组合的带上下文计算
--
-- 对应理论：范畴论、单子论

module Main where

import Control.Applicative
import Control.Monad

-- ============================================================
-- 第一部分：Functor（函子）
-- ============================================================

{- |
函子是一个可以"映射"的类型构造器。
数学定义：函子 F: C → D 是范畴 C 到 D 的映射。

在 Haskell 中，Functor 类型类定义了 fmap：
  fmap :: (a -> b) -> f a -> f b

Functor 定律：
1. 恒等律：fmap id = id
2. 复合律：fmap (f . g) = fmap f . fmap g
-}

-- Maybe Functor 的演示
demoMaybeFunctor :: IO ()
demoMaybeFunctor = do
    putStrLn "=== Maybe Functor ==="
    
    let just5 = Just 5
    let nothing = Nothing :: Maybe Int
    
    -- 使用 fmap 在 Maybe 上下文中应用函数
    putStrLn $ "fmap (+1) (Just 5) = " ++ show (fmap (+1) just5)
    putStrLn $ "fmap (+1) Nothing = " ++ show (fmap (+1) nothing)
    
    -- 中缀形式的 fmap <$> 更常用
    putStrLn $ "(+1) <$> Just 5 = " ++ show ((+1) <$> just5)
    putStrLn $ "show <$> Just 5 = " ++ show (show <$> just5)
    
    putStrLn ""

-- 列表 Functor
demoListFunctor :: IO ()
demoListFunctor = do
    putStrLn "=== List Functor ==="
    
    let numbers = [1, 2, 3, 4, 5]
    
    -- fmap 就是 map
    putStrLn $ "fmap (*2) [1,2,3] = " ++ show (fmap (*2) numbers)
    
    -- 嵌套 fmap
    let nested = [[1, 2], [3, 4], [5]]
    putStrLn $ "fmap (fmap (*2)) [[1,2],[3,4]] = " 
        ++ show (fmap (fmap (*2)) nested)
    
    putStrLn ""

-- 自定义 Functor：二叉树
data Tree a = Leaf a | Node (Tree a) a (Tree a)
    deriving (Show, Eq, Functor)  -- 使用 DeriveFunctor 自动派生

-- 手动实现 Functor（如果不使用 DeriveFunctor）
-- instance Functor Tree where
--     fmap f (Leaf x) = Leaf (f x)
--     fmap f (Node left x right) = Node (fmap f left) (f x) (fmap f right)

demoTreeFunctor :: IO ()
demoTreeFunctor = do
    putStrLn "=== Tree Functor ==="
    
    let tree = Node (Leaf 1) 2 (Node (Leaf 3) 4 (Leaf 5))
    putStrLn $ "Original tree: " ++ show tree
    putStrLn $ "fmap (*10) tree: " ++ show (fmap (*10) tree)
    putStrLn $ "fmap show tree: " ++ show (fmap show tree)
    
    putStrLn ""

-- ============================================================
-- 第二部分：Applicative（应用函子）
-- ============================================================

{- |
Applicative 是增强的 Functor，允许带上下文的函数应用。

核心操作：
  pure :: a -> f a          -- 将值放入上下文
  (<*>) :: f (a -> b) -> f a -> f b  -- 带上下文的函数应用

Applicative 定律：
1. 恒等律：pure id <*> v = v
2. 复合律：pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
3. 同态律：pure f <*> pure x = pure (f x)
4. 交换律：u <*> pure y = pure ($ y) <*> u
-}

demoMaybeApplicative :: IO ()
demoMaybeApplicative = do
    putStrLn "=== Maybe Applicative ==="
    
    -- pure 将值放入 Maybe 上下文
    putStrLn $ "pure 5 :: Maybe Int = " ++ show (pure 5 :: Maybe Int)
    
    -- <*> 应用带上下文的函数
    let justAdd = Just (+10)
    let just5 = Just 5
    putStrLn $ "Just (+10) <*> Just 5 = " ++ show (justAdd <*> just5)
    
    -- Nothing 传播
    putStrLn $ "Just (+10) <*> Nothing = " ++ show (Just (+10) <*> Nothing)
    putStrLn $ "Nothing <*> Just 5 = " ++ show (Nothing <*> just5)
    
    -- 多参数函数应用
    let add3 x y z = x + y + z
    putStrLn $ "add3 <$> Just 1 <*> Just 2 <*> Just 3 = " 
        ++ show (add3 <$> Just 1 <*> Just 2 <*> Just 3)
    
    putStrLn ""

demoListApplicative :: IO ()
demoListApplicative = do
    putStrLn "=== List Applicative ==="
    
    -- 列表的 <*> 产生笛卡尔积
    putStrLn $ "[(+1), (*2)] <*> [1, 2, 3] = " 
        ++ show ([(+1), (*2)] <*> [1, 2, 3])
    
    -- 这与列表推导式等价
    putStrLn $ "[f x | f <- [(+1), (*2)], x <- [1, 2, 3]] = "
        ++ show ([f x | f <- [(+1), (*2)], x <- [1, 2, 3]])
    
    -- ZipList：并行应用（使用 newtype）
    putStrLn $ "ZipList [(+1), (*2)] <*> ZipList [1, 2, 3] = "
        ++ show (getZipList $ ZipList [(+1), (*2)] <*> ZipList [1, 2, 3])
    
    putStrLn ""

-- 自定义 Applicative：Validation（累加错误）
data Validation e a = Failure e | Success a
    deriving (Show, Eq, Functor)

instance Semigroup e => Applicative (Validation e) where
    pure :: a -> Validation e a
    pure = Success
    
    (<*>) :: Validation e (a -> b) -> Validation e a -> Validation e b
    Success f <*> Success x = Success (f x)
    Failure e <*> Success _ = Failure e
    Success _ <*> Failure e = Failure e
    Failure e1 <*> Failure e2 = Failure (e1 <> e2)  -- 累加错误

demoValidation :: IO ()
demoValidation = do
    putStrLn "=== Validation Applicative ==="
    
    -- 累加多个错误
    let v1 = Failure ["error1"] :: Validation [String] Int
    let v2 = Failure ["error2"] :: Validation [String] Int
    let add = pure (+) :: Validation [String] (Int -> Int -> Int)
    
    putStrLn $ "Failure [\"error1\"] <*> Failure [\"error2\"] = "
        ++ show (add <*> v1 <*> v2)
    
    -- 成功情况
    putStrLn $ "pure (+) <*> Success 1 <*> Success 2 = "
        ++ show (pure (+) <*> Success 1 <*> Success 2)
    
    putStrLn ""

-- ============================================================
-- 第三部分：Monad（单子）
-- ============================================================

{- |
Monad 是增强的 Applicative，支持顺序组合（chaining）。

核心操作：
  return :: a -> m a          -- 同 pure
  (>>=) :: m a -> (a -> m b) -> m b  -- bind（绑定）
  (>>) :: m a -> m b -> m b   -- 序列，忽略第一个结果

Monad 定律：
1. 左单位元：return a >>= f = f a
2. 右单位元：m >>= return = m
3. 结合律：(m >>= f) >>= g = m >>= (\x -> f x >>= g)
-}

demoMaybeMonad :: IO ()
demoMaybeMonad = do
    putStrLn "=== Maybe Monad ==="
    
    -- 基本的 >>= 操作
    let result1 = Just 5 >>= (\x -> Just (x + 1))
    putStrLn $ "Just 5 >>= \\x -> Just (x + 1) = " ++ show result1
    
    -- 链式操作
    let result2 = Just 5 >>= (\x -> 
                  Just (x + 1) >>= (\y ->
                  Just (x + y)))
    putStrLn $ "链式操作结果 = " ++ show result2
    
    -- Nothing 短路
    let result3 = Nothing >>= (\x -> Just (x + 1))
    putStrLn $ "Nothing >>= \\x -> Just (x + 1) = " ++ show result3
    
    -- do 表示法（语法糖）
    let result4 = do
            x <- Just 5
            y <- Just (x + 1)
            return (x + y)
    putStrLn $ "使用 do 表示法: " ++ show result4
    
    putStrLn ""

demoListMonad :: IO ()
demoListMonad = do
    putStrLn "=== List Monad ==="
    
    -- 列表 Monad 模拟非确定性计算
    let pairs = do
            x <- [1, 2, 3]
            y <- [4, 5]
            return (x, y)
    putStrLn $ "笛卡尔积: " ++ show pairs
    
    -- 与列表推导式等价
    let pairs' = [(x, y) | x <- [1, 2, 3], y <- [4, 5]]
    putStrLn $ "列表推导式: " ++ show pairs'
    
    -- 带过滤的列表 Monad
    let evens = do
            x <- [1..10]
            guard (even x)
            return x
    putStrLn $ "偶数过滤: " ++ show evens
    
    putStrLn ""

-- 自定义 Monad：Writer（日志记录）
newtype Writer w a = Writer { runWriter :: (a, w) }
    deriving (Show)

instance Functor (Writer w) where
    fmap f (Writer (a, w)) = Writer (f a, w)

instance Monoid w => Applicative (Writer w) where
    pure a = Writer (a, mempty)
    Writer (f, w1) <*> Writer (a, w2) = Writer (f a, w1 <> w2)

instance Monoid w => Monad (Writer w) where
    return = pure
    Writer (a, w) >>= f = 
        let Writer (b, w') = f a
        in Writer (b, w <> w')

-- tell 函数：添加日志
tell :: w -> Writer w ()
tell w = Writer ((), w)

-- 示例：带日志的计算
calcWithLog :: Writer [String] Int
calcWithLog = do
    tell ["Starting calculation"]
    let x = 5
    tell ["x = " ++ show x]
    let y = x * 2
    tell ["y = x * 2 = " ++ show y]
    let z = y + 10
    tell ["z = y + 10 = " ++ show z]
    return z

demoWriterMonad :: IO ()
demoWriterMonad = do
    putStrLn "=== Writer Monad ==="
    
    let (result, log) = runWriter calcWithLog
    putStrLn $ "Result: " ++ show result
    putStrLn "Log:"
    mapM_ putStrLn log
    
    putStrLn ""

-- ============================================================
-- 第四部分：Monad 变换器
-- ============================================================

{- |
Monad 变换器允许组合多个 Monad 的效果。
常见变换器：
- MaybeT    - 添加 Maybe 效果
- ListT     - 添加 List 效果
- StateT    - 添加 State 效果
- WriterT   - 添加 Writer 效果
- ReaderT   - 添加 Reader 效果
- ExceptT   - 添加异常处理
-}

-- 简单的 State Monad
newtype State s a = State { runState :: s -> (a, s) }

instance Functor (State s) where
    fmap f (State g) = State $ \s -> let (a, s') = g s in (f a, s')

instance Applicative (State s) where
    pure a = State $ \s -> (a, s)
    State f <*> State g = State $ \s -> 
        let (f', s') = f s
            (a, s'') = g s'
        in (f' a, s'')

instance Monad (State s) where
    return = pure
    State f >>= g = State $ \s ->
        let (a, s') = f s
            State h = g a
        in h s'

-- State 操作
get :: State s s
get = State $ \s -> (s, s)

put :: s -> State s ()
put s = State $ \_ -> ((), s)

modify :: (s -> s) -> State s ()
modify f = do
    s <- get
    put (f s)

-- 示例：使用 State 实现计数器
increment :: State Int ()
increment = modify (+1)

counterExample :: State Int Int
counterExample = do
    increment
    increment
    n <- get
    increment
    return n

demoStateMonad :: IO ()
demoStateMonad = do
    putStrLn "=== State Monad ==="
    
    let (result, finalState) = runState counterExample 0
    putStrLn $ "Result: " ++ show result
    putStrLn $ "Final state: " ++ show finalState
    
    putStrLn ""

-- ============================================================
-- 第五部分：实际应用
-- ============================================================

-- 使用 Monad 实现安全的除法
safeDiv :: Double -> Double -> Maybe Double
safeDiv _ 0 = Nothing
safeDiv x y = Just (x / y)

-- 链式安全计算
calculate :: Maybe Double
calculate = do
    a <- Just 100
    b <- safeDiv a 2
    c <- safeDiv b 5
    return c

-- 使用 Either 处理错误（带错误信息）
safeDivE :: Double -> Double -> Either String Double
safeDivE _ 0 = Left "Division by zero"
safeDivE x y = Right (x / y)

calculateE :: Either String Double
calculateE = do
    a <- Right 100
    b <- safeDivE a 0  -- 这将返回 Left
    c <- safeDivE b 5
    return c

demoPractical :: IO ()
demoPractical = do
    putStrLn "=== 实际应用 ==="
    
    -- Maybe Monad 安全计算
    putStrLn $ "Safe calculation: " ++ show calculate
    
    -- Either Monad 错误处理
    putStrLn $ "Calculation with error: " ++ show calculateE
    
    -- IO Monad（Haskell 的主 Monad）
    putStrLn "IO Monad 示例:"
    result <- do
        putStrLn "  Enter something:"
        line <- getLine
        return ("You entered: " ++ line)
    putStrLn result
    
    putStrLn ""

-- ============================================================
-- 总结和输出
-- ============================================================

main :: IO ()
main = do
    putStrLn "╔══════════════════════════════════════════════════════════╗"
    putStrLn "║          Haskell 函子和单子示例                          ║"
    putStrLn "╚══════════════════════════════════════════════════════════╝"
    putStrLn ""
    
    demoMaybeFunctor
    demoListFunctor
    demoTreeFunctor
    demoMaybeApplicative
    demoListApplicative
    demoValidation
    demoMaybeMonad
    demoListMonad
    demoWriterMonad
    demoStateMonad
    demoPractical
    
    putStrLn "╔══════════════════════════════════════════════════════════╗"
    putStrLn "║          所有示例运行完成！                               ║"
    putStrLn "╚══════════════════════════════════════════════════════════╝"

{- 输出说明：

编译和运行：
```bash
ghc --make functor_monad.hs -o functor_monad
./functor_monad
```

或使用 runhaskell：
```bash
runhaskell functor_monad.hs
```

预期输出：
```
╔══════════════════════════════════════════════════════════╗
║          Haskell 函子和单子示例                          ║
╚══════════════════════════════════════════════════════════╝

=== Maybe Functor ===
fmap (+1) (Just 5) = Just 6
fmap (+1) Nothing = Nothing
...

╔══════════════════════════════════════════════════════════╗
║          所有示例运行完成！                               ║
╚══════════════════════════════════════════════════════════╝
```

理论对应：
- Functor ↔ 范畴论中的协变函子
- Applicative ↔ 强 lax 幺半函子
- Monad ↔ 单子（Triple/Triple）
- 单子变换器 ↔ 函子复合

Haskell 的 Monad 提供了：
- 计算上下文的抽象
- 副作用的纯函数表示
- 可组合的计算序列
- 强大的类型安全保证
-}
