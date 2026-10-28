//! Safe ownership reference: no Copy/Clone bound; no element cloning.
pub fn array_owned<T,const N:usize>(v:Vec<T>)->Result<[T;N],Vec<T>> {
    if v.len()!=N {return Err(v);}
    let mut iter=v.into_iter();
    Ok(core::array::from_fn(|_|iter.next().expect("length checked")))
}

#[cfg(test)] mod tests {
    use super::*;
    use std::{rc::Rc,cell::RefCell};
    struct Token {id:usize,drops:Rc<RefCell<Vec<usize>>>}
    impl Drop for Token {fn drop(&mut self) {self.drops.borrow_mut().push(self.id);}}
    fn one<const N:usize>(len:usize,reference:bool)->(bool,Vec<usize>,Vec<usize>) {
        let drops=Rc::new(RefCell::new(Vec::new()));
        let mut v=Vec::with_capacity(len+7);
        for id in 0..len {v.push(Token{id,drops:Rc::clone(&drops)});}
        let ptr=v.as_ptr();let capacity=v.capacity();
        let result=if reference {array_owned::<_,N>(v)} else {v.try_into()};
        assert!(drops.borrow().is_empty(),"conversion dropped a live element");
        let (success,ids)=match &result {
            Ok(a)=>(true,a.iter().map(|x|x.id).collect()),
            Err(v)=>{assert_eq!(v.as_ptr(),ptr);assert_eq!(v.capacity(),capacity);
                (false,v.iter().map(|x|x.id).collect())}
        };
        assert_eq!(success,len==N);
        assert_eq!(ids,(0..len).collect::<Vec<_>>());
        drop(result);
        let mut actual=drops.borrow().clone();actual.sort();
        assert_eq!(actual,(0..len).collect::<Vec<_>>(),"each element drops once");
        (success,ids,actual)
    }
    fn cases<const N:usize>() {
        for len in 0..=100 {assert_eq!(one::<N>(len,false),one::<N>(len,true));}
    }
    #[test] fn populated_noncopy_native_differential() {
        cases::<0>();cases::<1>();cases::<2>();cases::<7>();cases::<16>();cases::<64>();
        println!("606 same-input native/reference ownership cases, non-Copy Drop-bearing values; finite validation only");
    }
    thread_local!{static ZST_DROPS:std::cell::Cell<usize>=const{std::cell::Cell::new(0)};}
    struct Zst;
    impl Drop for Zst {fn drop(&mut self){ZST_DROPS.with(|n|n.set(n.get()+1));}}
    fn zst<const N:usize>(len:usize,reference:bool) {
        ZST_DROPS.with(|n|n.set(0));
        let v=(0..len).map(|_|Zst).collect::<Vec<_>>();
        let result=if reference {array_owned::<_,N>(v)}else{v.try_into()};
        ZST_DROPS.with(|n|assert_eq!(n.get(),0));
        assert_eq!(result.is_ok(),len==N);
        drop(result);ZST_DROPS.with(|n|assert_eq!(n.get(),len));
    }
    #[test] fn zero_size_drop_native_differential() {
        for len in 0..=32 {for reference in [false,true] {
            zst::<0>(len,reference);zst::<1>(len,reference);zst::<16>(len,reference);
        }}
        println!("99 paired ZST Drop-bearing cases; finite validation only");
    }
}
