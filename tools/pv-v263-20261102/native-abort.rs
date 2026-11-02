extern crate alloc;
#[path = "../../evidence/pv-v263-20261102/inputs/crates/aspis-r1-cost-probe/src/host_work.rs"]
mod host_work;
use std::io::Write;
use std::sync::{Arc,Mutex,Condvar};
fn main() {
    if std::env::args().nth(1).as_deref()==Some("success") {
        // Different coverage from N90121: panic=abort and nested ACTIVE TLS.
        for n in [0,2,27,28,14336] {
            let xs=host_work::map(200,n,|i| {
                let inner=host_work::map(201,2,|j| i*2+j);
                assert_eq!(inner,vec![i*2,i*2+1]);
                if i%7==0 {Err(i)} else {Ok(i)}
            });
            assert_eq!(xs,(0..n).map(|i|if i%7==0 {Err(i)} else {Ok(i)}).collect::<Vec<_>>());
            println!("abort-profile-nested-inner-results count={n}");
        }
        return;
    }
    let gate=Arc::new((Mutex::new(false),Condvar::new()));
    let mut handles=Vec::new();
    loop {
        let g=gate.clone();
        match std::thread::Builder::new().spawn(move||{
            let (lock,cv)=&*g;
            let mut released=lock.lock().unwrap();
            while !*released {released=cv.wait(released).unwrap();}
        }) {Ok(h)=>handles.push(h),Err(_)=>break}
    }
    println!("occupied={}",handles.len());
    std::io::stdout().flush().unwrap();
    let _=host_work::map(200,27,|i| {
        eprintln!("CALLBACK-EXECUTED index={i}");
        Ok::<usize,usize>(i)
    });
    // Expected unreachable: panic=abort kills this process and its threads.
    {let (lock,cv)=&*gate;*lock.lock().unwrap()=true;cv.notify_all();}
    for h in handles {h.join().unwrap();}
    println!("UNEXPECTED-RETURN");
}
