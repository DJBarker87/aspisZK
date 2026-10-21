#!/usr/bin/env python3
from pathlib import Path
E=Path(__file__).resolve().parent.parent
src=Path('crates/aspis-r1-cost-probe/src/r1_wire.rs').read_text()
extra=r'''
#[cfg(kani)]
mod callbacks12 {
    use super::*;
    static mut CALLS:usize=0;
    #[derive(Clone,Copy)]
    struct FrameObserver {state:[u8;32],row:u8,framed:*const u8,len:usize,answers:[[u8;32];3]}
    impl Digest32 for FrameObserver {
        fn digest(&self,parts:&[&[u8]])->[u8;32] {
            let call=unsafe {let c=CALLS;CALLS+=1;c};
            if call==0 {
                assert_eq!(parts.len(),3);
                assert_eq!(parts[0],&self.state);
                assert_eq!(parts[1],&[0,0xa0+self.row]);
                assert_eq!(parts[2].len(),self.len);
                assert_eq!(parts[2].as_ptr(),self.framed);
            } else {
                assert!(call<3);
                assert_eq!(parts.len(),2);
                assert_eq!(parts[0],&self.answers[0]);
                assert_eq!(parts[1],&[call as u8]);
            }
            self.answers[call]
        }
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn validated_block() {
        let framed:[u8;3717]=kani::any();
        let len:usize=kani::any();kani::assume(len<=3717);
        let row:u8=kani::any();kani::assume(row<=26);
        let expected_row:u8=kani::any();
        let state:[u8;32]=kani::any();let answers:[[u8;32];3]=kani::any();
        let h=FrameObserver{state,row,framed:framed.as_ptr(),len,answers};
        unsafe {CALLS=0;}
        let mut t=SemanticTranscript{state,hash:h,next_row:expected_row};
        let result=t.sample_block_validated(row,&framed[..len]);
        if row==expected_row {
            assert_eq!(result,Ok(answers[1]));
            assert_eq!(t.state,answers[2]);
            assert_eq!(t.next_row,row+1);
            unsafe {assert_eq!(CALLS,3);}
        } else {
            assert_eq!(result,Err(Error::RowOrder{expected:expected_row,actual:row}));
            assert_eq!(t.state,state);
            assert_eq!(t.next_row,expected_row);
            unsafe {assert_eq!(CALLS,0);}
        }
    }
    #[derive(Clone,Copy)]
    struct NewObserver {public:*const u8,len:usize,root:[u8;32],answer:[u8;32]}
    impl Digest32 for NewObserver {
        fn digest(&self,parts:&[&[u8]])->[u8;32] {
            assert_eq!(parts.len(),5);
            assert_eq!(parts[0],b"UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3");
            assert_eq!(parts[1],&[0]);
            assert_eq!(parts[2],&(self.len as u32).to_le_bytes());
            assert_eq!(parts[3].len(),self.len);
            assert_eq!(parts[3].as_ptr(),self.public);
            assert_eq!(parts[4],&self.root);
            unsafe {CALLS+=1;}
            self.answer
        }
    }
    #[kani::proof]
    #[kani::unwind(84)]
    fn semantic_new() {
        let public:[u8;4096]=kani::any();let len:usize=kani::any();kani::assume(len<=4096);
        let root:[u8;32]=kani::any();let answer:[u8;32]=kani::any();
        unsafe {CALLS=0;}
        let t=SemanticTranscript::new(NewObserver{public:public.as_ptr(),len,root,answer},&public[..len],&root).unwrap();
        assert_eq!(t.state,answer);
        assert_eq!(t.next_row,0);
        unsafe {assert_eq!(CALLS,1);}
    }
    #[kani::proof]
    fn row25_exceeds_old_rom() {
        let (_,bytes)=row_shape(25).unwrap();
        assert_eq!(bytes,3712);
        assert_eq!(32+2+5+bytes,3751);
        assert!(32+2+5+bytes>514);
    }
}
'''
(E/'rust-sources/r1_wire.rs').write_text(src+extra)
