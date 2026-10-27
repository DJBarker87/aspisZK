#![cfg_attr(kani,feature(formatting_options,io_error_more,io_error_inprogress,io_error_uncategorized))]
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

#[cfg(kani)]
#[kani::proof]
fn file_flush_borrowed_descriptor_value_and_frame() {
    use std::io::Write;
    use std::mem::ManuallyDrop;
    use std::os::fd::{AsRawFd, FromRawFd};
    // Valid File owners always have a nonnegative Unix descriptor. The
    // harness supplies only its scalar representation: OS ownership remains
    // a caller invariant, and no close/Drop contract is claimed here.
    let fd:i32=kani::any(); kani::assume(fd>=0);
    let frame_before:u64=kani::any();
    let frame_after:u64=kani::any();
    let mut file=ManuallyDrop::new(unsafe { std::fs::File::from_raw_fd(fd) });
    let before=(frame_before,frame_after);
    let result=Write::flush(&mut *file);
    assert!(result.is_ok());
    assert!(file.as_raw_fd()==fd);
    assert!(before==(frame_before,frame_after));
}

#[cfg(kani)]
#[kani::proof]
fn file_descriptor_owner_codec_roundtrip() {
    use std::mem::ManuallyDrop;
    use std::os::fd::{AsRawFd, FromRawFd, IntoRawFd};
    // The native caller supplies an owned open fd. Quantifying over every
    // nonnegative scalar covers its value representation without exercising
    // any OS operation or invalidating its retained external authority.
    let fd:i32=kani::any(); kani::assume(fd>=0);
    let file=unsafe { std::fs::File::from_raw_fd(fd) };
    assert!(file.as_raw_fd()==fd);
    let encoded=file.into_raw_fd();
    assert!(encoded==fd);
    let decoded=ManuallyDrop::new(unsafe { std::fs::File::from_raw_fd(encoded) });
    assert!(decoded.as_raw_fd()==fd);
    assert!(std::mem::size_of::<std::fs::File>()==std::mem::size_of::<i32>());
}

#[cfg(kani)]
mod file_close_link_transport {
    use std::sync::atomic::{AtomicI32,AtomicUsize,Ordering};
    use std::os::fd::FromRawFd;
    static CALLS:AtomicUsize=AtomicUsize::new(0);
    static FD:AtomicI32=AtomicI32::new(-1);
    // Bind the actual C ABI close symbol. The destructor itself is untouched;
    // only the OS primitive has nondeterministic replies and an observed call.
    #[unsafe(no_mangle)]
    #[inline(never)]
    pub unsafe extern "C" fn close(fd:i32)->i32 {
        FD.store(fd,Ordering::SeqCst);
        CALLS.fetch_add(1,Ordering::SeqCst);
        kani::any()
    }
    #[kani::proof]
    fn file_drop_one_close_cffi_rooted() {
        let fd:i32=kani::any();kani::assume(fd>=0);
        // Root the exported primitive body in MIR reachability before using
        // the foreign ABI name; reset and check its trace before real Drop.
        CALLS.store(0,Ordering::SeqCst);
        let _=unsafe {close(-9)};
        assert!(CALLS.load(Ordering::SeqCst)==1);
        assert!(FD.load(Ordering::SeqCst)==-9);
        CALLS.store(0,Ordering::SeqCst);
        FD.store(-1,Ordering::SeqCst);
        let file=unsafe {std::fs::File::from_raw_fd(fd)};
        let before:u64=kani::any();
        let after:u64=kani::any();
        let frame=(before,after);
        drop(file);
        assert!(frame==(before,after));
        assert!(CALLS.load(Ordering::SeqCst)==1);
        assert!(FD.load(Ordering::SeqCst)==fd);
    }
    #[kani::proof]
    fn file_codec_flush_and_drop_complete_lifetime() {
        use std::io::Write;
        use std::os::fd::{AsRawFd,IntoRawFd};
        let fd:i32=kani::any();kani::assume(fd>=0);
        CALLS.store(0,Ordering::SeqCst);
        let _=unsafe {close(-9)};
        assert!(CALLS.load(Ordering::SeqCst)==1);
        CALLS.store(0,Ordering::SeqCst);
        FD.store(-1,Ordering::SeqCst);
        let original=unsafe {std::fs::File::from_raw_fd(fd)};
        assert!(original.as_raw_fd()==fd);
        assert!(CALLS.load(Ordering::SeqCst)==0);
        let encoded=original.into_raw_fd();
        assert!(encoded==fd);
        assert!(CALLS.load(Ordering::SeqCst)==0);
        let mut decoded=unsafe {std::fs::File::from_raw_fd(encoded)};
        assert!(Write::flush(&mut decoded).is_ok());
        assert!(decoded.as_raw_fd()==fd);
        assert!(CALLS.load(Ordering::SeqCst)==0);
        drop(decoded);
        assert!(CALLS.load(Ordering::SeqCst)==1);
        assert!(FD.load(Ordering::SeqCst)==fd);
    }

}

#[cfg(kani)]
mod io_os_kind_scalar {
    use std::io::{Error,ErrorKind};
    fn expected(code:i32)->ErrorKind {
        match code {
            7=>ErrorKind::ArgumentListTooLong,
            98=>ErrorKind::AddrInUse,
            99=>ErrorKind::AddrNotAvailable,
            16=>ErrorKind::ResourceBusy,
            103=>ErrorKind::ConnectionAborted,
            111=>ErrorKind::ConnectionRefused,
            104=>ErrorKind::ConnectionReset,
            35=>ErrorKind::Deadlock,
            122=>ErrorKind::QuotaExceeded,
            17=>ErrorKind::AlreadyExists,
            27=>ErrorKind::FileTooLarge,
            113=>ErrorKind::HostUnreachable,
            4=>ErrorKind::Interrupted,
            22=>ErrorKind::InvalidInput,
            21=>ErrorKind::IsADirectory,
            40=>ErrorKind::FilesystemLoop,
            2=>ErrorKind::NotFound,
            12=>ErrorKind::OutOfMemory,
            28=>ErrorKind::StorageFull,
            38=>ErrorKind::Unsupported,
            31=>ErrorKind::TooManyLinks,
            36=>ErrorKind::InvalidFilename,
            100=>ErrorKind::NetworkDown,
            101=>ErrorKind::NetworkUnreachable,
            107=>ErrorKind::NotConnected,
            20=>ErrorKind::NotADirectory,
            39=>ErrorKind::DirectoryNotEmpty,
            32=>ErrorKind::BrokenPipe,
            30=>ErrorKind::ReadOnlyFilesystem,
            29=>ErrorKind::NotSeekable,
            116=>ErrorKind::StaleNetworkFileHandle,
            110=>ErrorKind::TimedOut,
            26=>ErrorKind::ExecutableFileBusy,
            18=>ErrorKind::CrossesDevices,
            115=>ErrorKind::InProgress,
            95=>ErrorKind::Unsupported,
            13 | 1=>ErrorKind::PermissionDenied,
            11=>ErrorKind::WouldBlock,
            _=>ErrorKind::Uncategorized,
        }
    }
    #[kani::proof]
    fn every_os_error_code_kind_and_payload() {
        let code:i32=kani::any();
        let error=Error::from_raw_os_error(code);
        assert!(error.raw_os_error()==Some(code));
        assert!(error.kind()==expected(code));
        assert!(error.get_ref().is_none());
    }
}

#[cfg(kani)]
mod io_simple_and_custom {
    use std::io::{Error,ErrorKind};
    use std::sync::atomic::{AtomicUsize,AtomicU64,Ordering};
    static DROPS:AtomicUsize=AtomicUsize::new(0);
    static DROPPED:AtomicU64=AtomicU64::new(0);
    fn kind(index:u8)->ErrorKind { match index {
        0=>ErrorKind::NotFound,
        1=>ErrorKind::PermissionDenied,
        2=>ErrorKind::ConnectionRefused,
        3=>ErrorKind::ConnectionReset,
        4=>ErrorKind::HostUnreachable,
        5=>ErrorKind::NetworkUnreachable,
        6=>ErrorKind::ConnectionAborted,
        7=>ErrorKind::NotConnected,
        8=>ErrorKind::AddrInUse,
        9=>ErrorKind::AddrNotAvailable,
        10=>ErrorKind::NetworkDown,
        11=>ErrorKind::BrokenPipe,
        12=>ErrorKind::AlreadyExists,
        13=>ErrorKind::WouldBlock,
        14=>ErrorKind::NotADirectory,
        15=>ErrorKind::IsADirectory,
        16=>ErrorKind::DirectoryNotEmpty,
        17=>ErrorKind::ReadOnlyFilesystem,
        18=>ErrorKind::FilesystemLoop,
        19=>ErrorKind::StaleNetworkFileHandle,
        20=>ErrorKind::InvalidInput,
        21=>ErrorKind::InvalidData,
        22=>ErrorKind::TimedOut,
        23=>ErrorKind::WriteZero,
        24=>ErrorKind::StorageFull,
        25=>ErrorKind::NotSeekable,
        26=>ErrorKind::QuotaExceeded,
        27=>ErrorKind::FileTooLarge,
        28=>ErrorKind::ResourceBusy,
        29=>ErrorKind::ExecutableFileBusy,
        30=>ErrorKind::Deadlock,
        31=>ErrorKind::CrossesDevices,
        32=>ErrorKind::TooManyLinks,
        33=>ErrorKind::InvalidFilename,
        34=>ErrorKind::ArgumentListTooLong,
        35=>ErrorKind::Interrupted,
        36=>ErrorKind::Unsupported,
        37=>ErrorKind::UnexpectedEof,
        38=>ErrorKind::OutOfMemory,
        39=>ErrorKind::InProgress,
        40=>ErrorKind::Other,
        _=>ErrorKind::Uncategorized,
    }}
    #[derive(Debug)]
    struct Payload(u64);
    impl std::fmt::Display for Payload {
        fn fmt(&self,_:&mut std::fmt::Formatter<'_>)->std::fmt::Result {
            panic!("kind accessor must not invoke payload Display")
        }
    }
    impl std::error::Error for Payload {}
    impl Drop for Payload {
        fn drop(&mut self) {
            DROPS.fetch_add(1,Ordering::SeqCst);
            DROPPED.store(self.0,Ordering::SeqCst);
        }
    }
    #[kani::proof]
    fn every_simple_kind_no_dynamic_payload() {
        let index:u8=kani::any();kani::assume(index<42);
        let k=kind(index);let error=Error::from(k);
        assert!(error.kind()==k);assert!(error.raw_os_error().is_none());
        assert!(error.get_ref().is_none());
    }
    #[kani::proof]
    fn every_custom_kind_payload_and_exact_drop() {
        let index:u8=kani::any();kani::assume(index<42);
        let bits:u64=kani::any();let frame:u64=kani::any();
        DROPS.store(0,Ordering::SeqCst);DROPPED.store(0,Ordering::SeqCst);
        let k=kind(index);let error=Error::new(k,Payload(bits));
        assert!(error.kind()==k);assert!(error.raw_os_error().is_none());
        assert!(error.get_ref().unwrap().downcast_ref::<Payload>().unwrap().0==bits);
        assert!(DROPS.load(Ordering::SeqCst)==0);
        drop(error);
        assert!(DROPS.load(Ordering::SeqCst)==1);
        assert!(DROPPED.load(Ordering::SeqCst)==bits);
        assert!(frame==frame);
    }
}

#[cfg(kani)]
mod formatter_split_options {
    use std::fmt::{self,Write,Debug,FormattingOptions,Alignment,Sign,DebugAsHex};
    fn options()->FormattingOptions {
        let mut opts=FormattingOptions::new();
        let sign:u8=kani::any();kani::assume(sign<3);
        opts.sign(match sign {0=>None,1=>Some(Sign::Plus),_=>Some(Sign::Minus)});
        let align:u8=kani::any();kani::assume(align<4);
        opts.align(match align {0=>None,1=>Some(Alignment::Left),2=>Some(Alignment::Right),_=>Some(Alignment::Center)});
        let hex:u8=kani::any();kani::assume(hex<3);
        opts.debug_as_hex(match hex {0=>None,1=>Some(DebugAsHex::Lower),_=>Some(DebugAsHex::Upper)});
        opts.fill(kani::any::<char>()).width(kani::any::<Option<u16>>())
            .precision(kani::any::<Option<u16>>()).alternate(kani::any())
            .sign_aware_zero_pad(kani::any());
        opts
    }
    fn run(index:u8) {
        use aspis_core::r0::Error::*;
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
        let fail:bool=kani::any();let frame:u64=kani::any();let opts=options();
        let mut sink=Sink{expected:name,fail,calls:0,frame};
        let result={
            let mut f=fmt::Formatter::new(&mut sink,opts);
            let r=Debug::fmt(&error,&mut f);
            assert!(f.options()==opts);r
        };
        assert!(sink.calls==1);assert!(sink.frame==frame);assert!(result.is_err()==fail);
    }
    #[kani::proof]
    fn variants_0_to_4_all_options() {let i:u8=kani::any();kani::assume(i<5);run(i);}
    #[kani::proof]
    fn variants_5_to_8_all_options() {let i:u8=kani::any();kani::assume(i>=5 && i<9);run(i);}
    #[kani::proof]
    fn variants_9_to_12_all_options() {let i:u8=kani::any();kani::assume(i>=9 && i<13);run(i);}
    #[kani::proof]
    fn variants_13_to_16_all_options() {let i:u8=kani::any();kani::assume(i>=13 && i<17);run(i);}
}

#[cfg(kani)]
mod formatter_extensional_options {
    use std::fmt::{self,Write,Debug,FormattingOptions,Alignment,Sign,DebugAsHex};
    fn options()->FormattingOptions {
        let mut opts=FormattingOptions::new();
        let sign:u8=kani::any();kani::assume(sign<3);
        opts.sign(match sign {0=>None,1=>Some(Sign::Plus),_=>Some(Sign::Minus)});
        let align:u8=kani::any();kani::assume(align<4);
        opts.align(match align {0=>None,1=>Some(Alignment::Left),2=>Some(Alignment::Right),_=>Some(Alignment::Center)});
        let hex:u8=kani::any();kani::assume(hex<3);
        opts.debug_as_hex(match hex {0=>None,1=>Some(DebugAsHex::Lower),_=>Some(DebugAsHex::Upper)});
        opts.fill(kani::any::<char>()).width(kani::any::<Option<u16>>())
            .precision(kani::any::<Option<u16>>()).alternate(kani::any())
            .sign_aware_zero_pad(kani::any());
        opts
    }
    fn run(index:u8) {
        use aspis_core::r0::Error::*;
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
        struct Sink { expected:&'static str, fail:bool, calls:u8, frame:u64, sample:usize }
        impl Write for Sink {
            fn write_str(&mut self,bytes:&str)->fmt::Result {
                assert!(bytes.len()==self.expected.len());
                assert!(bytes.as_bytes()[self.sample]==self.expected.as_bytes()[self.sample]);self.calls+=1;
                if self.fail {Err(fmt::Error)}else{Ok(())}
            }
        }
        let fail:bool=kani::any();let frame:u64=kani::any();let opts=options();
        let sample:usize=kani::any();kani::assume(sample<name.len());
        let mut sink=Sink{expected:name,fail,calls:0,frame,sample};
        let result={
            let mut f=fmt::Formatter::new(&mut sink,opts);
            let r=Debug::fmt(&error,&mut f);
            assert!(f.options()==opts);r
        };
        assert!(sink.calls==1);assert!(sink.frame==frame);assert!(result.is_err()==fail);
    }
    #[kani::proof]
    fn all_variants_one_arbitrary_byte_all_options() {let i:u8=kani::any();kani::assume(i<17);run(i);}
}

#[cfg(kani)]
mod publication_open_rejections {
    use std::fs::{File,OpenOptions};
    use std::io::ErrorKind;
    use std::os::unix::fs::OpenOptionsExt;
    #[kani::proof]
    fn no_access_mode_all_other_primitive_flags() {
        let mut options=OpenOptions::new();
        options.read(false).write(false).append(false)
            .truncate(kani::any()).create(kani::any()).create_new(kani::any())
            .mode(kani::any()).custom_flags(kani::any());
        match options.open("unreachable-before-os-open") {
            Ok(file)=>{std::mem::forget(file);panic!("invalid access mode unexpectedly opened")},
            Err(error)=>assert!(error.kind()==ErrorKind::InvalidInput),
        }
    }
    #[kani::proof]
    fn nul_path_rejected_before_os_open() {
        let mut bytes:[u8;16]=kani::any();
        for b in &mut bytes {*b &= 0x7f;}
        let position:usize=kani::any();kani::assume(position<16);
        bytes[position]=0;
        let path=std::str::from_utf8(&bytes).unwrap();
        match File::open(path) {
            Ok(file)=>{std::mem::forget(file);panic!("NUL path unexpectedly opened")},
            Err(error)=>assert!(error.kind()==ErrorKind::InvalidInput),
        }
    }
    #[kani::proof]
    fn no_access_mode_empty_path_all_other_flags() {
        let mut options=OpenOptions::new();
        options.read(false).write(false).append(false)
            .truncate(kani::any()).create(kani::any()).create_new(kani::any())
            .mode(kani::any()).custom_flags(kani::any());
        match options.open("") {
            Ok(file)=>{std::mem::forget(file);panic!("invalid access mode unexpectedly opened")},
            Err(error)=>assert!(error.kind()==ErrorKind::InvalidInput),
        }
    }
}

#[cfg(kani)]
mod owned_error;
#[cfg(kani)]
mod owned_error_checks {
    use super::owned_error::*;
    fn kind(index:u8)->ErrorKind { match index {
        0=>ErrorKind::NotFound,
        1=>ErrorKind::PermissionDenied,
        2=>ErrorKind::ConnectionRefused,
        3=>ErrorKind::ConnectionReset,
        4=>ErrorKind::HostUnreachable,
        5=>ErrorKind::NetworkUnreachable,
        6=>ErrorKind::ConnectionAborted,
        7=>ErrorKind::NotConnected,
        8=>ErrorKind::AddrInUse,
        9=>ErrorKind::AddrNotAvailable,
        10=>ErrorKind::NetworkDown,
        11=>ErrorKind::BrokenPipe,
        12=>ErrorKind::AlreadyExists,
        13=>ErrorKind::WouldBlock,
        14=>ErrorKind::NotADirectory,
        15=>ErrorKind::IsADirectory,
        16=>ErrorKind::DirectoryNotEmpty,
        17=>ErrorKind::ReadOnlyFilesystem,
        18=>ErrorKind::FilesystemLoop,
        19=>ErrorKind::StaleNetworkFileHandle,
        20=>ErrorKind::InvalidInput,
        21=>ErrorKind::InvalidData,
        22=>ErrorKind::TimedOut,
        23=>ErrorKind::WriteZero,
        24=>ErrorKind::StorageFull,
        25=>ErrorKind::NotSeekable,
        26=>ErrorKind::QuotaExceeded,
        27=>ErrorKind::FileTooLarge,
        28=>ErrorKind::ResourceBusy,
        29=>ErrorKind::ExecutableFileBusy,
        30=>ErrorKind::Deadlock,
        31=>ErrorKind::CrossesDevices,
        32=>ErrorKind::TooManyLinks,
        33=>ErrorKind::InvalidFilename,
        34=>ErrorKind::ArgumentListTooLong,
        35=>ErrorKind::Interrupted,
        36=>ErrorKind::Unsupported,
        37=>ErrorKind::UnexpectedEof,
        38=>ErrorKind::OutOfMemory,
        39=>ErrorKind::InProgress,
        40=>ErrorKind::Other,
        _=>ErrorKind::Uncategorized,
    }}
    use std::io::{Error,ErrorKind};
    fn check(error: Error) {
        let reference=OwnedError {kind:error.kind()};
        assert!(native_observe(Err(error)) == owned_observe(Err(reference)));
    }
    fn check_open(error: Error) {
        let reference=OwnedError {kind:error.kind()};
        assert!(native_observe(native_open_error(error)) == owned_observe(owned_open_error(reference)));
    }
    #[kani::proof]
    fn owned_error_os_kind_and_retry() { check_open(Error::from_raw_os_error(kani::any())); }
    #[kani::proof]
    fn owned_error_simple_kind_and_retry() {
        let i:u8=kani::any();kani::assume(i<42);
        check_open(Error::from(kind(i)));
    }
    #[kani::proof]
    fn owned_error_success_and_prior_error_reset() {
        let reserved:bool=kani::any();
        assert!(native_observe(Ok(reserved))==owned_observe(Ok(reserved)));
        assert!(owned_observe(Ok(reserved)).last_error.is_none());
    }
    #[kani::proof]
    fn owned_error_static_payload_kind_and_retry() {
        let i:u8=kani::any();kani::assume(i<42);
        check_open(Error::new(kind(i),"mask nonce ledger path is not a directory"));
    }
    #[kani::proof]
    fn owned_error_write_zero_kind_and_retry() { check_open(Error::from(ErrorKind::WriteZero)); }
    #[kani::proof]
    fn owned_error_os_observe() { check(Error::from_raw_os_error(kani::any())); }
    #[kani::proof]
    fn owned_error_simple_observe() {
        let i:u8=kani::any();kani::assume(i<42);
        check(Error::from(kind(i)));
    }
    #[kani::proof]
    fn owned_error_static_payload_observe() {
        check(Error::new(ErrorKind::NotADirectory,"mask nonce ledger path is not a directory"));
    }
}

#[cfg(kani)]
mod owned_dynamic_drop {
    use super::owned_error::*;
    use std::io::{Error,ErrorKind};
    use std::sync::atomic::{AtomicUsize,AtomicU64,Ordering};
    static DROPS:AtomicUsize=AtomicUsize::new(0);
    static PAYLOAD:AtomicU64=AtomicU64::new(0);
    #[derive(Debug)]
    struct Payload(u64);
    impl std::fmt::Display for Payload {
        fn fmt(&self,_:&mut std::fmt::Formatter<'_>)->std::fmt::Result {
            panic!("the reserve continuation does not consume payload messages")
        }
    }
    impl std::error::Error for Payload {}
    impl Drop for Payload {
        fn drop(&mut self) {
            DROPS.fetch_add(1,Ordering::SeqCst);
            PAYLOAD.store(self.0,Ordering::SeqCst);
        }
    }
    #[kani::proof]
    fn owned_custom_retry_observation_and_exact_drop() {
        let bits:u64=kani::any();
        let collision:bool=kani::any();
        let kind=if collision {ErrorKind::AlreadyExists} else {ErrorKind::Other};
        DROPS.store(0,Ordering::SeqCst);PAYLOAD.store(0,Ordering::SeqCst);
        let error=Error::new(kind,Payload(bits));
        let reference=OwnedError{kind};
        assert!(native_observe(native_open_error(error)) == owned_observe(owned_open_error(reference)));
        assert!(DROPS.load(Ordering::SeqCst)==1);
        assert!(PAYLOAD.load(Ordering::SeqCst)==bits);
    }
}

#[cfg(kani)]
mod file_sync_world {
    use std::sync::atomic::{AtomicI32,AtomicUsize,AtomicBool,Ordering};
    use std::os::fd::{FromRawFd,AsRawFd};
    use std::mem::ManuallyDrop;
    static CALLS:AtomicUsize=AtomicUsize::new(0);
    static FD:AtomicI32=AtomicI32::new(-1);
    static REPLY:AtomicI32=AtomicI32::new(0);
    static INTERRUPT_ONCE:AtomicBool=AtomicBool::new(false);
    static mut ERRNO:i32=0;
    #[unsafe(no_mangle)]
    #[inline(never)]
    pub unsafe extern "C" fn __errno_location()->*mut i32 { &raw mut ERRNO }
    #[unsafe(no_mangle)]
    #[inline(never)]
    pub unsafe extern "C" fn fsync(fd:i32)->i32 {
        let call=CALLS.fetch_add(1,Ordering::SeqCst);
        FD.store(fd,Ordering::SeqCst);
        if INTERRUPT_ONCE.load(Ordering::SeqCst) && call==0 {return -1;}
        REPLY.load(Ordering::SeqCst)
    }
    fn root() {
        INTERRUPT_ONCE.store(false,Ordering::SeqCst);
        REPLY.store(0,Ordering::SeqCst);
        let _=unsafe{fsync(-9)};
        unsafe{*__errno_location()=0};
        assert!(CALLS.load(Ordering::SeqCst)>0);
        CALLS.store(0,Ordering::SeqCst);FD.store(-1,Ordering::SeqCst);
    }
    #[kani::proof]
    #[kani::unwind(4)]
    fn sync_all_interrupted_then_success_world() {
        root();
        INTERRUPT_ONCE.store(true,Ordering::SeqCst);
        unsafe{*__errno_location()=4};
        let fd:i32=kani::any();kani::assume(fd>=0);
        let file=ManuallyDrop::new(unsafe{std::fs::File::from_raw_fd(fd)});
        assert!(file.sync_all().is_ok());
        assert!(CALLS.load(Ordering::SeqCst)==2);
        assert!(FD.load(Ordering::SeqCst)==fd && file.as_raw_fd()==fd);
    }
    #[kani::proof]
    fn sync_all_success_world_and_owner() {
        root();
        let fd:i32=kani::any();kani::assume(fd>=0);
        let file=ManuallyDrop::new(unsafe{std::fs::File::from_raw_fd(fd)});
        let result=file.sync_all();
        assert!(result.is_ok());
        assert!(CALLS.load(Ordering::SeqCst)==1);
        assert!(FD.load(Ordering::SeqCst)==fd);
        assert!(file.as_raw_fd()==fd);
    }
    #[kani::proof]
    #[kani::unwind(3)]
    fn sync_all_terminal_error_world_and_raw_code() {
        root();
        let fd:i32=kani::any();kani::assume(fd>=0);
        let code:i32=kani::any();kani::assume(code!=4);
        unsafe{*__errno_location()=code};
        REPLY.store(-1,Ordering::SeqCst);
        let file=ManuallyDrop::new(unsafe{std::fs::File::from_raw_fd(fd)});
        let error=file.sync_all().unwrap_err();
        assert!(error.raw_os_error()==Some(code));
        assert!(CALLS.load(Ordering::SeqCst)==1);
        assert!(FD.load(Ordering::SeqCst)==fd);
        assert!(file.as_raw_fd()==fd);
    }
}

#[cfg(kani)]
mod file_write_world {
    use std::sync::atomic::{AtomicI32,AtomicUsize,AtomicU8,Ordering};
    use std::os::fd::{FromRawFd,AsRawFd};
    use std::mem::ManuallyDrop;
    use std::io::{Write,ErrorKind};
    static CALLS:AtomicUsize=AtomicUsize::new(0);
    static FD:AtomicI32=AtomicI32::new(-1);
    static ACCEPTED:AtomicUsize=AtomicUsize::new(0);
    static POS:AtomicUsize=AtomicUsize::new(0);
    static BYTE:AtomicU8=AtomicU8::new(0);
    static MODE:AtomicUsize=AtomicUsize::new(0);
    static CUT:AtomicUsize=AtomicUsize::new(1);
    #[unsafe(no_mangle)]
    #[inline(never)]
    pub unsafe extern "C" fn write(fd:i32,buf:*const u8,count:usize)->isize {
        let call=CALLS.fetch_add(1,Ordering::SeqCst);
        FD.store(fd,Ordering::SeqCst);
        let mode=MODE.load(Ordering::SeqCst);
        if mode==1 {return 0;}
        if mode==2 {return -1;}
        if mode==3 && call==0 {return -1;}
        let amount=if mode==4 && call==0 {CUT.load(Ordering::SeqCst)} else {count};
        assert!(amount<=count);
        let accepted=ACCEPTED.load(Ordering::SeqCst);
        let position=POS.load(Ordering::SeqCst);
        if position>=accepted && position-accepted<amount {
            BYTE.store(unsafe{*buf.add(position-accepted)},Ordering::SeqCst);
        }
        ACCEPTED.store(accepted+amount,Ordering::SeqCst);
        amount as isize
    }
    fn root(mode:usize,errno:i32) {
        MODE.store(0,Ordering::SeqCst);CALLS.store(0,Ordering::SeqCst);
        ACCEPTED.store(0,Ordering::SeqCst);POS.store(0,Ordering::SeqCst);
        let result=unsafe{write(-9,std::ptr::null(),0)};
        assert!(result==0 && CALLS.load(Ordering::SeqCst)==1);
        unsafe{*super::file_sync_world::__errno_location()=errno};
        CALLS.store(0,Ordering::SeqCst);ACCEPTED.store(0,Ordering::SeqCst);
        MODE.store(mode,Ordering::SeqCst);
    }
    fn check_success(mode:usize) {
        root(mode,4);
        let fd:i32=kani::any();kani::assume(fd>=0);
        let data:[u8;32]=kani::any();
        let pos:usize=kani::any();kani::assume(pos<32);POS.store(pos,Ordering::SeqCst);
        let cut:usize=kani::any();kani::assume(cut>0 && cut<32);CUT.store(cut,Ordering::SeqCst);
        let mut file=ManuallyDrop::new(unsafe{std::fs::File::from_raw_fd(fd)});
        file.write_all(&data).unwrap();
        assert!(ACCEPTED.load(Ordering::SeqCst)==32);
        assert!(BYTE.load(Ordering::SeqCst)==data[pos]);
        assert!(FD.load(Ordering::SeqCst)==fd && file.as_raw_fd()==fd);
        assert!(CALLS.load(Ordering::SeqCst)==if mode==0 {1} else {2});
    }
    #[kani::proof]
    #[kani::unwind(3)]
    fn write_all_full_one_event() {check_success(0);}
    #[kani::proof]
    #[kani::unwind(4)]
    fn write_all_interrupted_then_full() {check_success(3);}
    #[kani::proof]
    #[kani::unwind(4)]
    fn write_all_partial_then_full() {check_success(4);}
    #[kani::proof]
    #[kani::unwind(3)]
    fn write_all_terminal_error_code_and_owner() {
        let code:i32=kani::any();kani::assume(code!=4);
        root(2,code);
        let fd:i32=kani::any();kani::assume(fd>=0);
        let data:[u8;32]=kani::any();
        let mut file=ManuallyDrop::new(unsafe{std::fs::File::from_raw_fd(fd)});
        let error=file.write_all(&data).unwrap_err();
        assert!(error.raw_os_error()==Some(code));
        assert!(CALLS.load(Ordering::SeqCst)==1);
        assert!(FD.load(Ordering::SeqCst)==fd);
        assert!(ACCEPTED.load(Ordering::SeqCst)==0 && file.as_raw_fd()==fd);
    }
    #[kani::proof]
    #[kani::unwind(3)]
    fn write_all_zero_error_preserves_owner() {
        root(1,0);
        let fd:i32=kani::any();kani::assume(fd>=0);
        let data:[u8;32]=kani::any();
        let mut file=ManuallyDrop::new(unsafe{std::fs::File::from_raw_fd(fd)});
        let error=file.write_all(&data).unwrap_err();
        assert!(error.kind()==ErrorKind::WriteZero);
        assert!(CALLS.load(Ordering::SeqCst)==1);
        assert!(ACCEPTED.load(Ordering::SeqCst)==0 && file.as_raw_fd()==fd);
    }
}
