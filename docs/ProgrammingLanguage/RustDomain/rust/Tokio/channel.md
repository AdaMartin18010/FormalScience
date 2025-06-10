# Tokio 通道类型及概念

以下是关于 Tokio 通道的类型、定义、概念、示例以及输出的思维导图和 Markdown 文档。

## 目录

- [Tokio 通道类型及概念](#tokio-通道类型及概念)
  - [目录](#目录)
  - [Tokio 通道](#tokio-通道)
    - [1. MPSC 通道（多生产者，单消费者）](#1-mpsc-通道多生产者单消费者)
    - [2. Oneshot 通道（单生产者，单消费者）](#2-oneshot-通道单生产者单消费者)
    - [3. Broadcast 通道（多生产者，多消费者）](#3-broadcast-通道多生产者多消费者)
    - [4. Watch 通道（单生产者，多消费者）](#4-watch-通道单生产者多消费者)
    - [Tokio 通道思维导图](#tokio-通道思维导图)
  - [Tokio 通道类型及使用](#tokio-通道类型及使用)
    - [1. MPSC 通道 （多生产者，单消费者）](#1-mpsc-通道-多生产者单消费者)
    - [2. Oneshot 通道 （单生产者，单消费者）](#2-oneshot-通道-单生产者单消费者)
    - [3. Broadcast 通道 （多生产者，多消费者）](#3-broadcast-通道-多生产者多消费者)
    - [4. Watch 通道 （单生产者，多消费者）](#4-watch-通道-单生产者多消费者)

## Tokio 通道

### 1. MPSC 通道（多生产者，单消费者）

    定义：允许多个生产者（Sender）向一个消费者（Receiver）发送消息。
    特点：
        支持有界（channel(capacity)）和无界（unbounded_channel()）两种形式。
        适用于多个任务向一个任务发送消息的场景。
        示例代码：

        ```rust
        use tokio::sync::mpsc;

        #[tokio::main]
        async fn main() {
            let (tx, mut rx) = mpsc::channel(10); // 有界通道，容量为10

            let tx1 = tx.clone();
            tokio::spawn(async move {
                tx1.send("Hello from task 1").await.unwrap();
            });

            let tx2 = tx.clone();
            tokio::spawn(async move {
                tx2.send("Hello from task 2").await.unwrap();
            });

            while let Some(msg) = rx.recv().await {
                println!("Received: {}", msg);
            }
        }
        ```

### 2. Oneshot 通道（单生产者，单消费者）

    定义：仅允许发送一次消息的通道，通常用于任务完成通知。
    特点：
        一次只能发送一个消息。
        适用于需要确认任务完成的场景。
        示例代码：

        ```rust
        use tokio::sync::oneshot;

        #[tokio::main]
        async fn main() {
            let (tx, rx) = oneshot::channel();

            tokio::spawn(async move {
                tx.send("Task completed").unwrap();
            });

            let msg = rx.await.unwrap();
            println!("{}", msg);
        }
        ```

### 3. Broadcast 通道（多生产者，多消费者）

    定义：允许多个生产者发送消息，多个消费者接收消息。
    特点：
        每个消息都会广播给所有消费者。
        适用于发布-订阅模式。
        示例代码：

        ```rust
        use tokio::sync::broadcast;

        #[tokio::main]
        async fn main() {
            let (tx, mut rx1) = broadcast::channel(16);
            let tx2 = tx.clone();

            tokio::spawn(async move {
                tx.send("Hello from tx1").unwrap();
            });

            tokio::spawn(async move {
                tx2.send("Hello from tx2").unwrap();
            });

            while let Ok(msg) = rx1.recv().await {
                println!("Received: {}", msg);
            }
        }
        ```

### 4. Watch 通道（单生产者，多消费者）

    定义：仅允许一个生产者发送消息，多个消费者接收消息。
    特点：
        只保留最新的消息。
        适用于配置更新或状态通知场景。
    示例代码：

    ```rust
    use tokio::sync::watch;

    #[tokio::main]
    async fn main() {
        let (tx, mut rx) = watch::channel("Initial value");

        tokio::spawn(async move {
            while rx.changed().await.is_ok() {
                println!("Received: {}", *rx.borrow());
            }
        });

        tx.send("New value").unwrap();
    }
    ```

### Tokio 通道思维导图

    ```text 
    mermaid
    graph TD
        A[Tokio Channels] --> B[MPSC]
        A --> C[Oneshot]
        A --> D[Broadcast]
        A --> E[Watch]

        B --> B1[多生产者，单消费者]
        B --> B2[有界/无界通道]
        B --> B3[适用于多任务向单任务发送消息]

        C --> C1[单生产者，单消费者]
        C --> C2[一次性发送]
        C --> C3[适用于任务完成通知]

        D --> D1[多生产者，多消费者]
        D --> D2[广播消息给所有消费者]
        D --> D3[适用于发布-订阅模式]

        E --> E1[单生产者，多消费者]
        E --> E2[只保留最新消息]
        E --> E3[适用于配置更新或状态通知]
    ```

Tokio Channels
MPSC
Oneshot
Broadcast
Watch
多生产者，单消费者
有界/无界通道
适用于多任务向单任务发送消息
单生产者，单消费者
一次性发送
适用于任务完成通知
多生产者，多消费者
广播消息给所有消费者
适用于发布-订阅模式
单生产者，多消费者
只保留最新消息
适用于配置更新或状态通知

## Tokio 通道类型及使用

### 1. MPSC 通道 （多生产者，单消费者）

**定义**：允许多个生产者向一个消费者发送消息。
**特点**：

- 支持有界和无界通道。
- 适用于多任务向单任务发送消息。

**示例代码**：

    ```rust
    use tokio::sync::mpsc;

    #[tokio::main]
    async fn main() {
        let (tx, mut rx) = mpsc::channel(10); // 有界通道，容量为10

        let tx1 = tx.clone();
        tokio::spawn(async move {
            tx1.send("Hello from task 1").await.unwrap();
        });

        let tx2 = tx.clone();
        tokio::spawn(async move {
            tx2.send("Hello from task 2").await.unwrap();
        });

        while let Some(msg) = rx.recv().await {
            println!("Received: {}", msg);
        }
    }
    ```

### 2. Oneshot 通道 （单生产者，单消费者）

    定义：仅允许发送一次消息的通道。
    特点：
        一次只能发送一个消息。
        适用于任务完成通知。
    示例代码：

    ```rust
    use tokio::sync::oneshot;

    #[tokio::main]
    async fn main() {
        let (tx, rx) = oneshot::channel();

        tokio::spawn(async move {
            tx.send("Task completed").unwrap();
        });

        let msg = rx.await.unwrap();
        println!("{}", msg);
    }
    ```

### 3. Broadcast 通道 （多生产者，多消费者）

    定义：允许多个生产者发送消息，多个消费者接收消息。
    特点：
        每个消息都会广播给所有消费者。
        适用于发布-订阅模式。
    示例代码：

    ```rust
    use tokio::sync::broadcast;

    #[tokio::main]
    async fn main() {
        let (tx, mut rx1) = broadcast::channel(16);
        let tx2 = tx.clone();

        tokio::spawn(async move {
            tx.send("Hello from tx1").unwrap();
        });

        tokio::spawn(async move {
            tx2.send("Hello from tx2").unwrap();
        });

        while let Ok(msg) = rx1.recv().await {
            println!("Received: {}", msg);
        }
    }
    ```

### 4. Watch 通道 （单生产者，多消费者）

    定义：仅允许一个生产者发送消息，多个消费者接收消息。
    特点：
        只保留最新的消息。
        适用于配置更新或状态通知。
    示例代码：

    ```rust
    use tokio::sync::watch;

    #[tokio::main]
    async fn main() {
        let (tx, mut rx) = watch::channel("Initial value");

        tokio::spawn(async move {
            while rx.changed().await.is_ok() {
                println!("Received: {}", *rx.borrow());
            }
        });

        tx.send("New value").unwrap();
    }
    ```

这些通道类型各有特点，适用于不同的场景需求。
开发者可以根据具体需求选择合适的通道类型
