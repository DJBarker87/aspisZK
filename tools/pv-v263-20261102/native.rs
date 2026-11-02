extern crate alloc;
#[path = "../../evidence/pv-v263-20261102/inputs/crates/aspis-r1-cost-probe/src/host_work.rs"]
mod host_work;
use std::sync::{Arc,Mutex,Condvar};
fn main() {
    let mode=std::env::args().nth(1).unwrap();
    if mode=="success" {
        for n in [0,28,56,112,224,448,896,1792,3584,7168,14336] {
            let xs=host_work::map(200,n,|i| if i%7==0 {Err(i)} else {Ok(i)});
            assert_eq!(xs,(0..n).map(|i|if i%7==0 {Err(i)} else {Ok(i)}).collect::<Vec<_>>());
            println!("ordered-inner-results count={n}");
        }
        let p=std::panic::catch_unwind(||host_work::map(200,28,|i| {
            if i==2 || i==17 {std::panic::panic_any(i);} i
        }));
        assert_eq!(*p.unwrap_err().downcast::<usize>().unwrap(),2);
        println!("first-source-order-panic=2; all handles joined");
    } else {
        // Fill THIS scope's task slots with local handles; no writable static,
        // no process outside this task, no environment or source mutation.
        let gate=Arc::new((Mutex::new(false),Condvar::new()));
        let mut handles=Vec::new();
        loop {
            let g=gate.clone();
            match std::thread::Builder::new().spawn(move||{
                let (lock,cv)=&*g;let mut released=lock.lock().unwrap();
                while !*released {released=cv.wait(released).unwrap();}
            }) {Ok(h)=>handles.push(h),Err(_)=>break}
        }
        let observed=std::panic::catch_unwind(||host_work::map(200,28,Ok::<usize,usize>));
        {let (lock,cv)=&*gate;*lock.lock().unwrap()=true;cv.notify_all();}
        let count=handles.len();
        for h in handles {h.join().unwrap();}
        println!("scope slots occupied by {count} retained local handles");
        assert!(observed.is_err(),"matched control: thread exhaustion must panic");
        println!("captured-stage=200 count=28: scope.spawn panics under task exhaustion");
    }
}
