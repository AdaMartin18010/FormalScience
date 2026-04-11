/**
 * Scala Actor模型示例
 *
 * 本文件演示Scala中的Actor模型编程：
 * - Actor基础
 * - 消息传递
 * - Actor生命周期
 * - 监督策略
 */

// ============================================
// Akka Actor依赖（build.sbt中添加）:
// libraryDependencies ++= Seq(
//   "com.typesafe.akka" %% "akka-actor-typed" % "2.8.5",
//   "com.typesafe.akka" %% "akka-actor-testkit-typed" % "2.8.5" % Test
// )
// ============================================

import java.util.concurrent.ConcurrentLinkedQueue
import scala.concurrent.{ExecutionContext, Future}
import scala.concurrent.duration._

// ============================================
// 1. 简化Actor系统演示
// ============================================

// 消息定义
sealed trait CalculatorMessage
case class Add(a: Int, b: Int, replyTo: Int => Unit) extends CalculatorMessage
case class Subtract(a: Int, b: Int, replyTo: Int => Unit) extends CalculatorMessage
case class Multiply(a: Int, b: Int, replyTo: Int => Unit) extends CalculatorMessage
case class Divide(a: Int, b: Int, replyTo: Either[String, Int] => Unit) extends CalculatorMessage

// 简化Actor实现
class SimpleCalculator(implicit ec: ExecutionContext) {
  private val mailbox = new ConcurrentLinkedQueue[CalculatorMessage]
  private var running = true

  // 启动处理循环
  Future {
    while (running) {
      Option(mailbox.poll()) match {
        case Some(message) => handle(message)
        case None => Thread.sleep(10)
      }
    }
  }

  private def handle(message: CalculatorMessage): Unit = message match {
    case Add(a, b, replyTo) =>
      println(s"[Calculator] Adding $a + $b")
      replyTo(a + b)

    case Subtract(a, b, replyTo) =>
      println(s"[Calculator] Subtracting $a - $b")
      replyTo(a - b)

    case Multiply(a, b, replyTo) =>
      println(s"[Calculator] Multiplying $a * $b")
      replyTo(a * b)

    case Divide(a, b, replyTo) =>
      println(s"[Calculator] Dividing $a / $b")
      if (b == 0) {
        replyTo(Left("Division by zero"))
      } else {
        replyTo(Right(a / b))
      }
  }

  def send(message: CalculatorMessage): Unit = mailbox.offer(message)
  def stop(): Unit = running = false
}

// 使用示例
object SimpleActorDemo extends App {
  println("=== 简化Actor演示 ===")

  implicit val ec: ExecutionContext = ExecutionContext.global

  val calculator = new SimpleCalculator

  // 发送消息
  calculator.send(Add(10, 5, result => println(s"Result: $result")))
  calculator.send(Subtract(20, 8, result => println(s"Result: $result")))
  calculator.send(Multiply(6, 7, result => println(s"Result: $result")))
  calculator.send(Divide(100, 4, {
    case Right(result) => println(s"Result: $result")
    case Left(error) => println(s"Error: $error")
  }))
  calculator.send(Divide(10, 0, {
    case Right(result) => println(s"Result: $result")
    case Left(error) => println(s"Error: $error")
  }))

  // 等待处理完成
  Thread.sleep(1000)
  calculator.stop()
}

// ============================================
// 2. Actor模式概念演示
// ============================================

// 状态机Actor模式
sealed trait ConnectionState
case object Disconnected extends ConnectionState
case object Connecting extends ConnectionState
case class Connected(sessionId: String) extends ConnectionState

sealed trait ConnectionMessage
case class Connect(address: String) extends ConnectionMessage
case object Disconnect extends ConnectionMessage
case class SendData(data: String) extends ConnectionMessage
case class ConnectionFailed(error: String) extends ConnectionMessage
case class ConnectionSuccess(sessionId: String) extends ConnectionMessage

class ConnectionActor {
  private var state: ConnectionState = Disconnected

  def receive(message: ConnectionMessage): Unit = {
    (state, message) match {
      // 从Disconnected状态
      case (Disconnected, Connect(address)) =>
        println(s"Connecting to $address...")
        state = Connecting
        simulateConnection(address)

      case (Disconnected, _) =>
        println("Cannot perform action: not connected")

      // 从Connecting状态
      case (Connecting, ConnectionSuccess(id)) =>
        println(s"Connected! Session ID: $id")
        state = Connected(id)

      case (Connecting, ConnectionFailed(error)) =>
        println(s"Connection failed: $error")
        state = Disconnected

      case (Connecting, _) =>
        println("Cannot perform action: connection in progress")

      // 从Connected状态
      case (Connected(sessionId), SendData(data)) =>
        println(s"[$sessionId] Sending: $data")

      case (Connected(_), Disconnect) =>
        println("Disconnecting...")
        state = Disconnected

      case (Connected(_), Connect(_)) =>
        println("Already connected")
    }
  }

  private def simulateConnection(address: String): Unit = {
    if (address.contains("valid")) {
      receive(ConnectionSuccess(s"session-${System.currentTimeMillis()}"))
    } else {
      receive(ConnectionFailed("Invalid address"))
    }
  }
}

object StateMachineDemo extends App {
  println("\n=== 状态机Actor模式 ===")

  val connection = new ConnectionActor

  // 尝试在断开状态下发送数据
  connection.receive(SendData("hello"))

  // 连接
  connection.receive(Connect("valid.server.com"))

  // 发送数据
  connection.receive(SendData("Hello, Server!"))

  // 断开
  connection.receive(Disconnect)

  // 失败的连接
  connection.receive(Connect("invalid.server"))
}

// ============================================
// 3. 父子Actor和监督策略（概念演示）
// ============================================

// 监督策略
trait SupervisorStrategy
object ResumeStrategy extends SupervisorStrategy
object RestartStrategy extends SupervisorStrategy
object StopStrategy extends SupervisorStrategy
object EscalateStrategy extends SupervisorStrategy

// 工作任务
case class WorkTask(id: String, work: () => Unit)

// 工作Actor事件
trait WorkerEvent
case class Completed(taskId: String) extends WorkerEvent
case class Failed(taskId: String, error: Throwable) extends WorkerEvent

// Worker特质
trait ActorRef[-T] {
  def !(message: T): Unit
}

// 工作Actor
class Worker(val id: String, supervisor: ActorRef[WorkerEvent]) {
  def execute(task: WorkTask): Unit = {
    try {
      task.work()
      supervisor ! Completed(task.id)
    } catch {
      case e: Exception =>
        supervisor ! Failed(task.id, e)
    }
  }
}

// 监督Actor
class SupervisorActor(strategy: SupervisorStrategy) {
  private val workers = scala.collection.mutable.Map[String, Worker]()
  private var failedTasks = 0

  def createWorker(id: String): Worker = {
    val worker = new Worker(id, this)
    workers(id) = worker
    worker
  }

  def handleFailure(workerId: String, error: Throwable): Unit = {
    failedTasks += 1
    println(s"Worker $workerId failed: ${error.getMessage}")

    strategy match {
      case ResumeStrategy =>
        println("Resuming worker...")

      case RestartStrategy =>
        println("Restarting worker...")
        workers.remove(workerId)
        createWorker(workerId)

      case StopStrategy =>
        println("Stopping worker...")
        workers.remove(workerId)

      case EscalateStrategy =>
        println("Escalating to parent...")
    }
  }

  def !(event: WorkerEvent): Unit = event match {
    case Completed(taskId) =>
      println(s"Task $taskId completed successfully")

    case Failed(taskId, error) =>
      handleFailure(taskId, error)
  }

  def failedCount: Int = failedTasks
}

object SupervisionDemo extends App {
  println("\n=== 监督策略演示 ===")

  val supervisor = new SupervisorActor(RestartStrategy)
  val worker = supervisor.createWorker("worker-1")

  // 成功任务
  worker.execute(WorkTask("task-1", () => println("Task 1 executed")))

  // 失败任务
  worker.execute(WorkTask("task-2", () => throw new RuntimeException("Oops!")))

  // 查看监督者状态
  println(s"Failed tasks: ${supervisor.failedCount}")
}

// ============================================
// 4. Actor设计模式
// ============================================

// 请求-响应模式
object RequestResponsePattern {
  case class Request(id: String, payload: String)
  case class Response(requestId: String, result: String)

  class ServiceActor {
    def process(request: Request, replyTo: Response => Unit): Unit = {
      val result = s"Processed: ${request.payload}"
      replyTo(Response(request.id, result))
    }
  }
}

// Pub-Sub模式
object PubSubPattern {
  trait Event
  case class Subscribe(subscriber: Event => Unit)
  case class Unsubscribe(subscriber: Event => Unit)
  case class Publish(event: Event)
  case class UserEvent(userId: String, action: String) extends Event

  class EventBus {
    private val subscribers = scala.collection.mutable.Set[Event => Unit]()

    def subscribe(subscriber: Event => Unit): Unit = {
      subscribers += subscriber
    }

    def unsubscribe(subscriber: Event => Unit): Unit = {
      subscribers -= subscriber
    }

    def publish(event: Event): Unit = {
      subscribers.foreach(_(event))
    }
  }
}

// 路由模式
object RouterPattern {
  trait Routable {
    def routeKey: String
  }
}

// 示例使用
object DesignPatternsDemo extends App {
  println("\n=== Actor设计模式 ===")

  // Request-Response
  val service = new RequestResponsePattern.ServiceActor
  service.process(
    RequestResponsePattern.Request("req-1", "Hello"),
    response => println(s"Received: $response")
  )

  // Pub-Sub
  val eventBus = new PubSubPattern.EventBus

  val subscriber1: PubSubPattern.Event => Unit = event => println(s"Subscriber 1: $event")
  val subscriber2: PubSubPattern.Event => Unit = event => println(s"Subscriber 2: $event")

  eventBus.subscribe(subscriber1)
  eventBus.subscribe(subscriber2)

  eventBus.publish(PubSubPattern.UserEvent("user-1", "login"))

  eventBus.unsubscribe(subscriber2)
  eventBus.publish(PubSubPattern.UserEvent("user-1", "logout"))
}

// ============================================
// 5. Actor最佳实践
// ============================================

object ActorBestPractices {
  // 1. 消息应该是不可变的
  case class ImmutableMessage(value: String, timestamp: Long)

  // 2. 使用密封特质定义消息
  sealed trait MyActorMessage
  case class DoWork(data: String) extends MyActorMessage
  case object Stop extends MyActorMessage
  case class GetStatus(replyTo: ActorRef[StatusResponse]) extends MyActorMessage
  case class StatusResponse(state: String)

  // 3. 不要阻塞Actor
  // 使用Future和回调来处理长时间运行的操作

  // 4. 妥善处理生命周期
  // 在preStart中初始化资源
  // 在postStop中清理资源
}

// ============================================
// 主程序
// ============================================

object ActorModel extends App {
  println("========================================")
  println("Scala Actor模型示例")
  println("========================================")
  println("注意：这是概念演示，真正的Akka Actor需要额外依赖")
  println()

  SimpleActorDemo.main(Array())
  StateMachineDemo.main(Array())
  SupervisionDemo.main(Array())
  DesignPatternsDemo.main(Array())

  println("\n========================================")
  println("所有Actor模型演示完成")
  println("========================================")
  println()
  println("要使用真正的Akka Actor，请添加以下依赖到build.sbt:")
  println("libraryDependencies += \"com.typesafe.akka\" %% \"akka-actor-typed\" % \"2.8.5\"")
}
