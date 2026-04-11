/**
 * Scala 类型类示例
 *
 * 本文件演示Scala中的类型类模式：
 * - 类型类定义
 * - 隐式实例
 * - 扩展方法
 * - 类型类推导
 */

// ============================================
// 1. 类型类基础
// ============================================

// 定义类型类
// Scala 3 使用 given/using，Scala 2 使用 implicit
// 这里展示兼容两种版本的写法

// 可序列化类型类
trait Serializable[A] {
  def serialize(value: A): String
  def deserialize(data: String): A
}

// 可比较类型类
trait Comparable[A] {
  def compare(x: A, y: A): Int
  def lt(x: A, y: A): Boolean = compare(x, y) < 0
  def gt(x: A, y: A): Boolean = compare(x, y) > 0
  def eq(x: A, y: A): Boolean = compare(x, y) == 0
}

// 可展示类型类（Show typeclass）
trait Show[A] {
  def show(value: A): String
}

// 半群（有结合律的二元运算）
trait Semigroup[A] {
  def combine(x: A, y: A): A
}

// 幺半群（有单位元的半群）
trait Monoid[A] extends Semigroup[A] {
  def empty: A
}

// 函子（可映射的结构）
trait Functor[F[_]] {
  def map[A, B](fa: F[A])(f: A => B): F[B]
}

// ============================================
// 2. 类型类实例（Scala 2风格）
// ============================================

object TypeClassInstances {
  // String的Show实例
  implicit val stringShow: Show[String] = new Show[String] {
    def show(value: String): String = value
  }

  // Int的Show实例
  implicit val intShow: Show[Int] = new Show[Int] {
    def show(value: Int): String = value.toString
  }

  // List的Show实例（递归）
  implicit def listShow[A](implicit showA: Show[A]): Show[List[A]] =
    new Show[List[A]] {
      def show(value: List[A]): String =
        value.map(showA.show).mkString("[", ", ", "]")
    }

  // Int的Monoid实例
  implicit val intMonoid: Monoid[Int] = new Monoid[Int] {
    def empty: Int = 0
    def combine(x: Int, y: Int): Int = x + y
  }

  // String的Monoid实例
  implicit val stringMonoid: Monoid[String] = new Monoid[String] {
    def empty: String = ""
    def combine(x: String, y: String): String = x + y
  }

  // List的Monoid实例
  implicit def listMonoid[A]: Monoid[List[A]] = new Monoid[List[A]] {
    def empty: List[A] = Nil
    def combine(x: List[A], y: List[A]): List[A] = x ++ y
  }

  // Option的Monoid实例
  implicit def optionMonoid[A](implicit monoidA: Monoid[A]): Monoid[Option[A]] =
    new Monoid[Option[A]] {
      def empty: Option[A] = None
      def combine(x: Option[A], y: Option[A]): Option[A] = (x, y) match {
        case (None, b) => b
        case (a, None) => a
        case (Some(a), Some(b)) => Some(monoidA.combine(a, b))
      }
    }

  // List的Functor实例
  implicit val listFunctor: Functor[List] = new Functor[List] {
    def map[A, B](fa: List[A])(f: A => B): List[B] = fa.map(f)
  }

  // Option的Functor实例
  implicit val optionFunctor: Functor[Option] = new Functor[Option] {
    def map[A, B](fa: Option[A])(f: A => B): Option[B] = fa.map(f)
  }
}

// ============================================
// 3. 类型类用法
// ============================================

object TypeClassUsage {
  import TypeClassInstances._

  // 使用类型类（上下文边界语法）
  def printShow[A: Show](value: A): Unit = {
    val showInstance = implicitly[Show[A]]
    println(showInstance.show(value))
  }

  // 使用类型类（隐式参数语法）
  def combineAll[A](values: List[A])(implicit monoid: Monoid[A]): A =
    values.foldLeft(monoid.empty)(monoid.combine)

  // 组合多个类型类
  def formatAndSum[A: Show: Monoid](values: List[A]): String = {
    val showA = implicitly[Show[A]]
    val monoidA = implicitly[Monoid[A]]
    val sum = values.foldLeft(monoidA.empty)(monoidA.combine)
    s"Sum of ${values.map(showA.show).mkString(", ")} = ${showA.show(sum)}"
  }

  // 使用Functor
  def doubleAll[F[_]: Functor](container: F[Int]): F[Int] = {
    val functor = implicitly[Functor[F]]
    functor.map(container)(_ * 2)
  }
}

// ============================================
// 4. 扩展方法（隐式类）
// ============================================

object TypeClassSyntax {
  // 为任何有Show实例的类型添加show方法
  implicit class ShowOps[A](value: A) {
    def show(implicit instance: Show[A]): String = instance.show(value)
  }

  // 为任何有Monoid实例的类型添加combine方法
  implicit class SemigroupOps[A](value: A) {
    def |+|(other: A)(implicit instance: Semigroup[A]): A =
      instance.combine(value, other)
  }

  // 为Functor容器添加map方法
  implicit class FunctorOps[F[_], A](container: F[A]) {
    def mapF[B](f: A => B)(implicit instance: Functor[F]): F[B] =
      instance.map(container)(f)
  }
}

// ============================================
// 5. 类型类演示
// ============================================

object TypeClassDemo extends App {
  println("=== 类型类演示 ===")

  import TypeClassInstances._
  import TypeClassUsage._
  import TypeClassSyntax._

  // Show类型类演示
  println("\n--- Show类型类 ---")
  printShow("Hello, World!")
  printShow(42)
  printShow(List(1, 2, 3))
  printShow(List("a", "b", "c"))

  // 使用扩展方法
  println(s"\"test\".show = ${"test".show}")
  println(s"123.show = ${123.show}")

  // Monoid类型类演示
  println("\n--- Monoid类型类 ---")
  val numbers = List(1, 2, 3, 4, 5)
  println(s"combineAll(numbers): ${combineAll(numbers)}")

  val strings = List("Hello", ", ", "World", "!")
  println(s"combineAll(strings): ${combineAll(strings)}")

  // 使用 |+| 运算符
  println(s"3 |+| 4 = ${3 |+| 4}")
  println(s"\"hello\" |+| \" world\" = ${"hello" |+| " world"}")
  println(s"List(1,2) |+| List(3,4) = ${List(1, 2) |+| List(3, 4)}")

  // Option的Monoid
  val opt1: Option[Int] = Some(10)
  val opt2: Option[Int] = Some(20)
  val opt3: Option[Int] = None

  println(s"Some(10) |+| Some(20) = ${opt1 |+| opt2}")
  println(s"Some(10) |+| None = ${opt1 |+| opt3}")

  // Functor类型类演示
  println("\n--- Functor类型类 ---")
  val list = List(1, 2, 3, 4, 5)
  println(s"doubleAll(list): ${doubleAll(list)}")

  val opt = Option(42)
  println(s"doubleAll(opt): ${doubleAll(opt)}")

  // 使用扩展方法
  println(s"list.mapF(_ * 3): ${list.mapF(_ * 3)}")
  println(s"opt.mapF(_ + 1): ${opt.mapF(_ + 1)}")

  // 组合使用
  println("\n--- 组合使用 ---")
  println(formatAndSum(List(1, 2, 3)))
  println(formatAndSum(List("a", "b", "c")))
}

// ============================================
// 6. 自定义数据类型的类型类实例
// ============================================

case class Person(name: String, age: Int)
case class Point(x: Double, y: Double)

// 为自定义类型创建类型类实例
object CustomInstances {
  // Person的Show实例
  implicit val personShow: Show[Person] = new Show[Person] {
    def show(value: Person): String = s"${value.name}(${value.age})"
  }

  // Person的Comparable实例
  implicit val personComparable: Comparable[Person] = new Comparable[Person] {
    def compare(x: Person, y: Person): Int = x.age.compareTo(y.age)
  }

  // Point的Show实例
  implicit val pointShow: Show[Point] = new Show[Point] {
    def show(value: Point): String = s"(${value.x}, ${value.y})"
  }

  // Point的Monoid实例（向量加法）
  implicit val pointMonoid: Monoid[Point] = new Monoid[Point] {
    def empty: Point = Point(0, 0)
    def combine(x: Point, y: Point): Point =
      Point(x.x + y.x, x.y + y.y)
  }
}

// ============================================
// 7. 类型类推导
// ============================================

object TypeClassDerivation extends App {
  println("\n=== 自定义类型类型类演示 ===")

  import TypeClassInstances._
  import TypeClassSyntax._
  import CustomInstances._

  val alice = Person("Alice", 30)
  val bob = Person("Bob", 25)

  println(s"Alice: ${alice.show}")
  println(s"Bob: ${bob.show}")

  val p1 = Point(1.0, 2.0)
  val p2 = Point(3.0, 4.0)

  println(s"p1: ${p1.show}")
  println(s"p2: ${p2.show}")
  println(s"p1 |+| p2 = ${(p1 |+| p2).show}")

  // 使用通用函数
  def sortByAge(people: List[Person])(implicit comp: Comparable[Person]): List[Person] =
    people.sortWith(comp.lt)

  val people = List(
    Person("Charlie", 35),
    Person("Alice", 30),
    Person("Bob", 25)
  )

  println(s"\n排序前: ${people.map(_.show)}")
  println(s"排序后: ${sortByAge(people).map(_.show)}")
}

// ============================================
// 8. 高级类型类模式
// ============================================

// 逆变类型类
// Contravariant类型类：如果A可以转化为B，那么F[B]可以转化为F[A]
trait Contravariant[F[_]] {
  def contramap[A, B](fa: F[A])(f: B => A): F[B]
}

// Show是Contravariant的
trait ShowContravariant extends Contravariant[Show] {
  def contramap[A, B](fa: Show[A])(f: B => A): Show[B] =
    new Show[B] {
      def show(value: B): String = fa.show(f(value))
    }
}

// 双变类型类（Bifunctor）
trait Bifunctor[F[_, _]] {
  def bimap[A, B, C, D](fab: F[A, B])(f: A => C, g: B => D): F[C, D]
}

// Either的Bifunctor实例
implicit val eitherBifunctor: Bifunctor[Either] = new Bifunctor[Either] {
  def bimap[A, B, C, D](fab: Either[A, B])(f: A => C, g: B => D): Either[C, D] =
    fab match {
      case Left(a) => Left(f(a))
      case Right(b) => Right(g(b))
    }
}

// 类型类组合
// 将多个类型类组合成一个
trait Numeric[A] extends Monoid[A] with Comparable[A] {
  def multiply(x: A, y: A): A
  def negate(x: A): A
  def fromInt(n: Int): A
}

// 为Int创建Numeric实例
implicit val intNumeric: Numeric[Int] = new Numeric[Int] {
  // Monoid
  def empty: Int = 0
  def combine(x: Int, y: Int): Int = x + y

  // Comparable
  def compare(x: Int, y: Int): Int = x.compareTo(y)

  // Numeric特有
  def multiply(x: Int, y: Int): Int = x * y
  def negate(x: Int): Int = -x
  def fromInt(n: Int): Int = n
}

// 使用Numeric类型类
object NumericUsage {
  def sumOfSquares[A: Numeric](values: List[A]): A = {
    val numeric = implicitly[Numeric[A]]
    values.foldLeft(numeric.empty) { (acc, x) =>
      numeric.combine(acc, numeric.multiply(x, x))
    }
  }
}

// 演示高级模式
object AdvancedPatterns extends App {
  println("\n=== 高级类型类模式 ===")

  import NumericUsage._

  val nums = List(1, 2, 3, 4, 5)
  println(s"sumOfSquares($nums) = ${sumOfSquares(nums)}")

  // 使用Either的bimap
  val either: Either[String, Int] = Right(42)
  val transformed = eitherBifunctor.bimap(either)(
    s => s.toUpperCase,
    n => n * 2
  )
  println(s"bimap result: $transformed")

  val leftEither: Either[String, Int] = Left("error")
  val transformedLeft = eitherBifunctor.bimap(leftEither)(
    s => s.toUpperCase,
    n => n * 2
  )
  println(s"bimap left result: $transformedLeft")
}

// ============================================
// 主程序
// ============================================

object TypeClasses extends App {
  println("========================================")
  println("Scala 类型类示例")
  println("========================================")

  TypeClassDemo.main(Array())
  TypeClassDerivation.main(Array())
  AdvancedPatterns.main(Array())

  println("\n========================================")
  println("所有类型类演示完成")
  println("========================================")
}
