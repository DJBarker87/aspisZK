#!/usr/bin/env python3
from pathlib import Path
E=Path(__file__).resolve().parent.parent
src=Path('crates/aspis-r1-cost-probe/src/multiproof.rs').read_text()
extra=r'''
#[cfg(kani)]
mod callbacks12 {
    use super::*;
    static mut CALLS:usize=0;
    #[derive(Clone,Copy)]
    struct Observer{left:[u8;32],right:[u8;32],answer:[u8;32]}
    impl Digest32 for Observer {
        fn digest(&self,parts:&[&[u8]])->[u8;32] {
            assert_eq!(parts.len(),3);
            assert_eq!(parts[0],&[0x12]);
            assert_eq!(parts[1],&self.left);
            assert_eq!(parts[2],&self.right);
            unsafe {CALLS+=1;}
            self.answer
        }
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn node() {
        let left:[u8;32]=kani::any();let right:[u8;32]=kani::any();let answer:[u8;32]=kani::any();
        unsafe {CALLS=0;}
        assert_eq!(binary_parent(Observer{left,right,answer},&left,&right),answer);
        unsafe {assert_eq!(CALLS,1);}
    }
}
'''
(E/'rust-sources/multiproof.rs').write_text(src+extra)
