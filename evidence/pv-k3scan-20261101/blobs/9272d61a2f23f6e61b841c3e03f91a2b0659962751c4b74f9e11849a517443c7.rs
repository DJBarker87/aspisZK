include!("move-reference.rs");

#[cfg(kani)]
mod checks {
    use super::*;
    #[kani::proof]
    #[kani::unwind(6)]
    fn pop_noncopy_result() {
        let bytes: [u8;4] = kani::any();
        let tags: [bool;4] = kani::any();
        let n:usize=kani::any();kani::assume(n<=4);
        let mut a:Vec<Result<Vec<u8>,Vec<u8>>>=Vec::with_capacity(5);
        let mut b:Vec<Result<Vec<u8>,Vec<u8>>>=Vec::with_capacity(5);
        let mut i=0;
        while i<n {
            let x=if tags[i] {Ok(vec![bytes[i]])} else {Err(vec![bytes[i]])};
            a.push(x.clone());b.push(x);i+=1;
        }
        let ap=a.as_ptr();let ac=a.capacity();
        let bp=b.as_ptr();let bc=b.capacity();
        let x=a.pop();let y=pop_move_reference(&mut b);
        assert_eq!(x,y);assert_eq!(a,b);
        assert_eq!(a.as_ptr(),ap);assert_eq!(a.capacity(),ac);
        assert_eq!(b.as_ptr(),bp);assert_eq!(b.capacity(),bc);
    }
}
