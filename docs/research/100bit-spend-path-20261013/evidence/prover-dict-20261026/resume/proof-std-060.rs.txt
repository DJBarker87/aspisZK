#![cfg_attr(kani,feature(formatting_options))]
#[cfg(kani)]
#[kani::proof]
fn formatter_direct_sink_error_and_frame() {
    use std::fmt::{self,Write};
    struct Sink { fail:bool, called:bool, before:u64 }
    impl Write for Sink {
        fn write_str(&mut self,s:&str)->fmt::Result {
            assert!(s=="x"); self.called=true;
            if self.fail {Err(fmt::Error)} else {Ok(())}
        }
    }
    let fail:bool=kani::any();
    let before:u64=kani::any();
    let mut sink=Sink{fail,called:false,before};
    let result={
        let mut formatter=fmt::Formatter::new(&mut sink,fmt::FormattingOptions::new());
        formatter.write_str("x")
    };
    assert!(sink.called);
    assert!(result.is_err()==fail);
    assert!(sink.before==before);
}

#[cfg(kani)]
#[kani::proof]
fn compiler_fence_valid_order_frame() {
    use core::sync::atomic::{compiler_fence,Ordering};
    let choice:u8=kani::any();kani::assume(choice<4);
    let order=match choice {0=>Ordering::Acquire,1=>Ordering::Release,2=>Ordering::AcqRel,_=>Ordering::SeqCst};
    let before:[u8;32]=kani::any();let after=before;
    compiler_fence(order);
    assert!(before==after);
}

#[cfg(kani)]
#[kani::proof]
#[kani::should_panic]
#[allow(invalid_atomic_ordering)]
fn compiler_fence_relaxed_has_panic() {
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::Relaxed);
}
