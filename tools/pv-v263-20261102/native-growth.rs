// Finite validation of the handle Vec growth plan. Representative payloads;
// this does not execute runjoin's actual encoder or SemanticOracle closures.
use std::mem::{size_of,align_of};
use std::thread::ScopedJoinHandle;
fn check<T:Send+'static>(label:&str, corrupt:bool) {
    std::thread::scope(|scope| {
        let mut handles=Vec::new();
        let mut observed=[0usize;15];
        let mut changes=Vec::new();
        for k in 1..16 {
            let old_capacity=handles.capacity();
            let old_pointer=handles.as_ptr() as usize;
            let task=scope.spawn(|| std::panic::catch_unwind(|| {
                let values:Vec<T>=Vec::new();
                vec![(values,0i32)]
            }));
            handles.push(task);
            let new_capacity=handles.capacity();
            observed[k-1]=new_capacity;
            if new_capacity!=old_capacity {changes.push(new_capacity);}
            else {assert_eq!(handles.as_ptr() as usize,old_pointer);}
        }
        type Packet<T> = std::thread::Result<Vec<(Vec<T>,i32)>>;
        let size=size_of::<ScopedJoinHandle<'_,Packet<T>>>();
        let align=align_of::<ScopedJoinHandle<'_,Packet<T>>>();
        let mut cap=0;let mut expected=Vec::new();
        for length in 0..15 {
            if length==cap {
                let min=if size==1 {8} else if size<=1024 {4} else {1};
                let min=if corrupt {min+1} else {min};
                cap=min.max((cap*2).max(cap+1));expected.push(cap);
            }
            assert_eq!(observed[length],cap);
        }
        assert_eq!(changes,expected);
        for task in handles {assert!(task.join().unwrap().is_ok());}
        println!("{{\"label\":\"{}\",\"handle_size\":{},\"handle_align\":{},\"capacities\":{:?},\"growth_requests\":{:?}}}",label,size,align,observed,changes);
    });
}
fn main() {
    let corrupt=std::env::args().any(|a| a=="--bad-growth");
    check::<u8>("u8",corrupt);
    check::<Result<[u32;4],u8>>("representative-field-result",corrupt);
    check::<[u8;4096]>("large-payload",corrupt);
}
