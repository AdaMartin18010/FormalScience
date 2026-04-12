//! # Future 和异步状态机

use std::future::Future as StdFuture;
use std::pin::Pin;
use std::task::{Context, Poll};

/// 自定义 Future trait
pub trait Future {
    type Output;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}

/// 立即完成的 Future
pub struct Ready<T>(Option<T>);

impl<T> Ready<T> {
    pub fn new(value: T) -> Self {
        Ready(Some(value))
    }
}

impl<T> Future for Ready<T> {
    type Output = T;
    
    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<T> {
        let this = unsafe { self.get_unchecked_mut() };
        Poll::Ready(this.0.take().expect("poll called after completion"))
    }
}

/// 阻塞等待 Future 完成
pub fn block_on<F: StdFuture>(future: F) -> F::Output {
    use std::sync::Arc;
    use std::task::Wake;
    use std::thread;

    struct DummyWaker;
    
    impl Wake for DummyWaker {
        fn wake(self: Arc<Self>) {}
        fn wake_by_ref(self: &Arc<Self>) {}
    }
    
    let waker = Arc::new(DummyWaker).into();
    let mut context = Context::from_waker(&waker);
    
    let mut future = std::pin::pin!(future);
    
    loop {
        match future.as_mut().poll(&mut context) {
            Poll::Ready(result) => return result,
            Poll::Pending => {
                thread::yield_now();
            }
        }
    }
}

/// 异步 sleep
pub struct Sleep {
    deadline: std::time::Instant,
}

impl Sleep {
    pub fn new(duration: std::time::Duration) -> Self {
        Self {
            deadline: std::time::Instant::now() + duration,
        }
    }
}

impl Future for Sleep {
    type Output = ();
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if std::time::Instant::now() >= self.deadline {
            Poll::Ready(())
        } else {
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_ready() {
        let result = block_on(FromStd::new(async { 42 }));
        assert_eq!(result, 42);
    }
    
    fn std_future_adapter<F: Future>(f: F) -> impl StdFuture<Output = F::Output> {
        struct Adapter<F>(Option<F>);
        
        impl<F: Future> StdFuture for Adapter<F> {
            type Output = F::Output;
            
            fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let this = unsafe { self.get_unchecked_mut() };
                if let Some(f) = &mut this.0 {
                    match unsafe { Pin::new_unchecked(f) }.poll(cx) {
                        Poll::Ready(r) => {
                            this.0 = None;
                            Poll::Ready(r)
                        }
                        Poll::Pending => Poll::Pending,
                    }
                } else {
                    panic!("polled after completion")
                }
            }
        }
        
        Adapter(Some(f))
    }
    
    use std::future::Future as StdFuture;
}

/// 将标准库的 Future 转换为我们的 Future
pub struct FromStd<F>(F);

impl<F> FromStd<F> {
    pub fn new(future: F) -> Self {
        Self(future)
    }
}

impl<F: StdFuture> Future for FromStd<F> {
    type Output = F::Output;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = unsafe { self.map_unchecked_mut(|s| &mut s.0) };
        this.poll(cx)
    }
}
