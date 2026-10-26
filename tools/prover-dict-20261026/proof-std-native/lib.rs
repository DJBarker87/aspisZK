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

#[cfg(kani)]
#[kani::proof]
fn native_r0_debug_sink_trace() {
    use std::fmt::{self,Write,Debug};
    use aspis_core::r0::Error::*;
    let index:u8=kani::any(); kani::assume(index<17);
    let (error,name)=match index {
        0=>(IndexOutOfRange,"IndexOutOfRange"),1=>(WrongLength,"WrongLength"),
        2=>(ZeroDenominator,"ZeroDenominator"),3=>(Allocation,"Allocation"),
        4=>(NonCanonical,"NonCanonical"),5=>(WrongField,"WrongField"),
        6=>(InvalidPoints,"InvalidPoints"),7=>(QuotientNotInImage,"QuotientNotInImage"),
        8=>(RankDeficient,"RankDeficient"),9=>(Parse,"Parse"),
        10=>(Semantic,"Semantic"),11=>(Schedule,"Schedule"),12=>(Sampler,"Sampler"),
        13=>(Commitment,"Commitment"),14=>(Authentication,"Authentication"),
        15=>(V1,"V1"),_=>(V2,"V2")
    };
    struct Sink { expected:&'static str, fail:bool, calls:u8, frame:u64 }
    impl Write for Sink {
        fn write_str(&mut self,bytes:&str)->fmt::Result {
            assert!(bytes==self.expected);self.calls+=1;
            if self.fail {Err(fmt::Error)}else{Ok(())}
        }
    }
    let fail:bool=kani::any();let frame:u64=kani::any();
    let mut sink=Sink{expected:name,fail,calls:0,frame};
    let result={
        let mut f=fmt::Formatter::new(&mut sink,fmt::FormattingOptions::new());
        Debug::fmt(&error,&mut f)
    };
    assert!(sink.calls==1);assert!(sink.frame==frame);assert!(result.is_err()==fail);
}
