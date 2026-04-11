/**
 * Scala 函数式编程示例
 *
 * 本文件演示Scala中的函数式编程：
 * - 高阶函数
 * - 不可变数据结构
 * - 模式匹配
 * - for推导式
 */

// ============================================
// 1. 函数基础
// ============================================

object FunctionBasics extends App {
  println("=== 函数基础 ===")

  // 函数字面量（Lambda）
  val add = (a: Int, b: Int) => a + b
  val multiply = (a: Int, b: Int) => a * b

  println(s"2 + 3 = ${add(2, 3)}")
  println(s"4 * 5 = ${multiply(4, 5)}")

  // 柯里化
  val curriedAdd = (a: Int) => (b: Int) => a + b
  val add5 = curriedAdd(5)
  println(s"add5(10) = ${add5(10)}")

  // 部分应用
  val multiplyBy3 = multiply.curried(3)
  println(s"multiplyBy3(4) = ${multiplyBy3(4)}")

  // 函数组合
  val increment = (x: Int) => x + 1
  val double = (x: Int) => x * 2
  val incrementThenDouble = increment andThen double
  val doubleThenIncrement = increment compose double

  println(s"incrementThenDouble(5) = ${incrementThenDouble(5)}") // (5 + 1) * 2 = 12
  println(s"doubleThenIncrement(5) = ${doubleThenIncrement(5)}") // 5 * 2 + 1 = 11
}

// ============================================
// 2. 高阶函数
// ============================================

object HigherOrderFunctions extends App {
  println("\n=== 高阶函数 ===")

  // map, filter, reduce
  val numbers = List(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)

  val doubled = numbers.map(_ * 2)
  println(s" doubled: $doubled")

  val evens = numbers.filter(_ % 2 == 0)
  println(s"evens: $evens")

  val sum = numbers.reduce(_ + _)
  println(s"sum: $sum")

  // flatMap
  val nested = List(List(1, 2), List(3, 4), List(5, 6))
  val flattened = nested.flatMap(identity)
  println(s"flattened: $flattened")

  // foldLeft / foldRight
  val product = numbers.foldLeft(1)(_ * _)
  println(s"product: $product")

  val reverse = numbers.foldLeft(List.empty[Int])((acc, x) => x :: acc)
  println(s"reverse: $reverse")

  // groupBy
  val grouped = numbers.groupBy(_ % 3)
  println(s"grouped by mod 3: $grouped")

  // scan（前缀扫描）
  val runningSum = numbers.scanLeft(0)(_ + _)
  println(s"running sum: $runningSum")

  // 自定义高阶函数
  def applyTwice(f: Int => Int, x: Int): Int = f(f(x))
  println(s"applyTwice(_ + 1, 5) = ${applyTwice(_ + 1, 5)}")

  // 返回函数的函数
  def makeMultiplier(factor: Int): Int => Int = (x: Int) => x * factor
  val triple = makeMultiplier(3)
  println(s"triple(4) = ${triple(4)}")
}

// ============================================
// 3. 不可变数据结构
// ============================================

object ImmutableDataStructures extends App {
  println("\n=== 不可变数据结构 ===")

  // List - 不可变链表
  val list1 = List(1, 2, 3)
  val list2 = 0 :: list1  // 前置元素（高效）
  val list3 = list1 :+ 4  // 追加元素（需要复制）

  println(s"list1: $list1")
  println(s"list2 (0 :: list1): $list2")
  println(s"list3 (list1 :+ 4): $list3")

  // Vector - 不可变索引序列（高效的随机访问）
  val vec1 = Vector(1, 2, 3)
  val vec2 = vec1 :+ 4    // 末尾添加（高效）
  val vec3 = 0 +: vec1    // 开头添加（高效）
  val vec4 = vec1.updated(1, 99)  // 更新（高效）

  println(s"vec1: $vec1")
  println(s"vec2 (append): $vec2")
  println(s"vec3 (prepend): $vec3")
  println(s"vec4 (updated): $vec4")

  // Set - 不可变集合
  val set1 = Set(1, 2, 3, 3, 3)  // 自动去重
  val set2 = set1 + 4
  val set3 = set1 - 2
  val set4 = set1 ++ Set(3, 4, 5)

  println(s"set1: $set1")
  println(s"set2 (+ 4): $set2")
  println(s"set3 (- 2): $set3")
  println(s"set4 (union): $set4")

  // Map - 不可变映射
  val map1 = Map("a" -> 1, "b" -> 2, "c" -> 3)
  val map2 = map1 + ("d" -> 4)
  val map3 = map1.updated("b", 20)
  val map4 = map1 - "a"

  println(s"map1: $map1")
  println(s"map2 (+ d): $map2")
  println(s"map3 (updated b): $map3")
  println(s"map4 (- a): $map4")

  // 获取值（返回Option）
  val value1 = map1.get("a")  // Some(1)
  val value2 = map1.get("z")  // None
  val value3 = map1.getOrElse("z", 0)  // 0

  println(s"get 'a': $value1")
  println(s"get 'z': $value2")
  println(s"getOrElse 'z': $value3")

  // 自定义不可变类（case class自动不可变）
  case class Person(name: String, age: Int) {
    def withAge(newAge: Int): Person = copy(age = newAge)
    def isAdult: Boolean = age >= 18
  }

  val alice = Person("Alice", 30)
  val olderAlice = alice.withAge(31)

  println(s"alice: $alice")
  println(s"olderAlice: $olderAlice")
  println(s"alice unchanged: $alice")  // 原始对象未被修改

  // 持久化数据结构 - 共享结构
  val bigList = (1 to 1000).toList
  val modifiedList = 0 :: bigList
  println(s"bigList length: ${bigList.length}")
  println(s"modifiedList length: ${modifiedList.length}")
  // 内部共享大部分结构
}

// ============================================
// 4. 模式匹配
// ============================================

object PatternMatching extends App {
  println("\n=== 模式匹配 ===")

  // 基本匹配
  def describe(x: Any): String = x match {
    case 1 => "one"
    case "hello" => "greeting"
    case y: Int => s"an integer: $y"
    case s: String => s"a string: $s"
    case list: List[_] => s"a list with ${list.length} elements"
    case null => "null value"
    case _ => "unknown"
  }

  println(describe(1))
  println(describe("hello"))
  println(describe(42))
  println(describe(List(1, 2, 3)))
  println(describe(3.14))

  // case class匹配（解构）
  case class Point(x: Int, y: Int)
  case class Circle(center: Point, radius: Double)
  case class Rectangle(topLeft: Point, width: Double, height: Double)

  def describeShape(shape: Any): String = shape match {
    case Circle(Point(0, 0), radius) =>
      s"Circle at origin with radius $radius"
    case Circle(center, radius) =>
      s"Circle at $center with radius $radius"
    case Rectangle(_, w, h) if w == h =>
      s"Square with side $w"
    case Rectangle(Point(x, y), w, h) =>
      s"Rectangle at ($x, $y) with width $w and height $h"
    case Point(x, y) =>
      s"Point at ($x, $y)"
    case _ => "Unknown shape"
  }

  println(describeShape(Circle(Point(0, 0), 5)))
  println(describeShape(Circle(Point(1, 1), 3)))
  println(describeShape(Rectangle(Point(0, 0), 10, 10)))
  println(describeShape(Rectangle(Point(1, 1), 5, 3)))

  // 列表模式匹配
  def listAnalysis(list: List[Int]): String = list match {
    case Nil => "Empty list"
    case head :: Nil => s"Single element: $head"
    case first :: second :: _ => s"First two: $first, $second"
  }

  println(listAnalysis(List()))
  println(listAnalysis(List(42)))
  println(listAnalysis(List(1, 2, 3, 4)))

  // 提取器模式（unapply）
  object Even {
    def unapply(n: Int): Option[Int] =
      if (n % 2 == 0) Some(n / 2) else None
  }

  object Positive {
    def unapply(n: Int): Boolean = n > 0
  }

  def analyzeNumber(n: Int): String = n match {
    case Even(half) => s"Even number, half is $half"
    case Positive() => s"Positive odd number"
    case _ => s"Negative or zero"
  }

  println(analyzeNumber(10))
  println(analyzeNumber(7))
  println(analyzeNumber(-5))

  // 偏函数
  val evenSquares: PartialFunction[Int, Int] = {
    case x if x % 2 == 0 => x * x
  }

  val numbers = List(1, 2, 3, 4, 5, 6)
  println(s"even squares: ${numbers.collect(evenSquares)}")

  // 模式匹配与for推导式结合
  val pairs = List((1, "one"), (2, "two"), (3, "three"))
  val descriptions = for {
    (num, str) <- pairs
    if num > 1
  } yield s"$num is $str"
  println(s"descriptions: $descriptions")
}

// ============================================
// 5. for推导式
// ============================================

object ForComprehensions extends App {
  println("\n=== for推导式 ===")

  // 基础用法（等效于map）
  val numbers = List(1, 2, 3, 4, 5)
  val squares = for (n <- numbers) yield n * n
  println(s"squares: $squares")

  // 带守卫（等效于filter + map）
  val evenSquares = for {
    n <- numbers
    if n % 2 == 0
  } yield n * n
  println(s"even squares: $evenSquares")

  // 多个生成器（嵌套循环）
  val coordinates = for {
    x <- 1 to 3
    y <- 1 to 3
  } yield (x, y)
  println(s"coordinates: $coordinates")

  // 带守卫的嵌套循环
  val uniquePairs = for {
    x <- 1 to 3
    y <- 1 to 3
    if x < y
  } yield (x, y)
  println(s"unique pairs: $uniquePairs")

  // 绑定中间结果
  val result = for {
    x <- List(1, 2, 3)
    y = x * 2
    z = y + 1
  } yield z
  println(s"bound variables: $result")

  // 处理Option
  def parseInt(s: String): Option[Int] =
    try Some(s.toInt)
    catch { case _: NumberFormatException => None }

  val parsed = for {
    a <- parseInt("10")
    b <- parseInt("20")
    c <- parseInt("30")
  } yield a + b + c
  println(s"parsed sum: $parsed")

  val failedParse = for {
    a <- parseInt("10")
    b <- parseInt("abc")  // 这将返回None
    c <- parseInt("30")
  } yield a + b + c
  println(s"failed parse: $failedParse")

  // 处理多个Option
  val nameOpt: Option[String] = Some("Alice")
  val ageOpt: Option[Int] = Some(30)

  val personInfo = for {
    name <- nameOpt
    age <- ageOpt
  } yield s"$name is $age years old"
  println(s"person info: $personInfo")

  // 处理List和Option混合（使用toList转换）
  val mixed = for {
    x <- List(1, 2, 3)
    y <- Some(x * 2).toList
  } yield y
  println(s"mixed: $mixed")

  // for推导式与模式匹配
  val pairs = List((1, "a"), (2, "b"), (3, "c"))
  val strings = for {
    (num, str) <- pairs
    if num > 1
  } yield s"$num-$str"
  println(s"pattern matched: $strings")
}

// ============================================
// 6. 递归和尾递归
// ============================================

object Recursion extends App {
  println("\n=== 递归和尾递归 ===")

  // 普通递归（栈安全）
  def factorial(n: Int): Int =
    if (n <= 1) 1
    else n * factorial(n - 1)

  println(s"factorial(5): ${factorial(5)}")

  // 尾递归优化
  def factorialTailRec(n: Int): BigInt = {
    @annotation.tailrec
    def loop(n: Int, acc: BigInt): BigInt =
      if (n <= 1) acc
      else loop(n - 1, acc * n)

    loop(n, 1)
  }

  println(s"factorialTailRec(20): ${factorialTailRec(20)}")

  // 尾递归处理列表
  def reverseList[A](list: List[A]): List[A] = {
    @annotation.tailrec
    def loop(remaining: List[A], acc: List[A]): List[A] =
      remaining match {
        case Nil => acc
        case head :: tail => loop(tail, head :: acc)
      }

    loop(list, Nil)
  }

  val myList = List(1, 2, 3, 4, 5)
  println(s"reverse ${myList}: ${reverseList(myList)}")

  // 尾递归实现map
  def mapList[A, B](list: List[A])(f: A => B): List[B] = {
    @annotation.tailrec
    def loop(remaining: List[A], acc: List[B]): List[B] =
      remaining match {
        case Nil => acc.reverse
        case head :: tail => loop(tail, f(head) :: acc)
      }

    loop(list, Nil)
  }

  println(s"mapList(_ * 2): ${mapList(myList)(_ * 2)}")

  // 间接递归
  def even(n: Int): Boolean =
    if (n == 0) true
    else odd(n - 1)

  def odd(n: Int): Boolean =
    if (n == 0) false
    else even(n - 1)

  println(s"even(10): ${even(10)}")
  println(s"odd(7): ${odd(7)}")
}

// ============================================
// 主程序
// ============================================

object FunctionalProgramming extends App {
  println("========================================")
  println("Scala 函数式编程示例")
  println("========================================")

  FunctionBasics.main(Array())
  HigherOrderFunctions.main(Array())
  ImmutableDataStructures.main(Array())
  PatternMatching.main(Array())
  ForComprehensions.main(Array())
  Recursion.main(Array())

  println("\n========================================")
  println("所有函数式编程演示完成")
  println("========================================")
}
