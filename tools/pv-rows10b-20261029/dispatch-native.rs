fn main() {
    let mut first=[0u8;64];
    let mut second=[0u8;64];
    let a=getrandom::fill(&mut first);
    let b=getrandom::fill(&mut second);
    let counts=unsafe {
        let p=libc::dlsym(libc::RTLD_DEFAULT,b"pv_dispatch_counts\0".as_ptr().cast());
        if p.is_null(){0} else {
            let f:unsafe extern "C" fn()->u64=std::mem::transmute(p); f()
        }
    };
    println!("{{\"first_ok\":{},\"second_ok\":{},\"first_errno\":{},\"second_errno\":{},\"first_changed\":{},\"second_changed\":{},\"probe_count\":{},\"draw_count\":{}}}",
        a.is_ok(),b.is_ok(),a.err().and_then(|e|e.raw_os_error()).unwrap_or(0),
        b.err().and_then(|e|e.raw_os_error()).unwrap_or(0),first!=[0;64],second!=[0;64],counts>>32,counts&0xffff_ffff);
}
