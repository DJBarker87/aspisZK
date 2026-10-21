#!/usr/bin/env python3
from pathlib import Path
E=Path(__file__).resolve().parent.parent
src=Path('crates/aspis-r1-cost-probe/src/transcript.rs').read_text()
extra=r'''
#[cfg(kani)]
mod callbacks12 {
    use super::*;
    static mut CALLS: usize = 0;
    // These are arbitrary response traces, not fresh independent oracle
    // samples. Framing is proved even for traces outside the deterministic
    // oracle subclass; no probability assertion is made by these harnesses.
    #[derive(Clone,Copy)]
    struct AbsorbObserver {
        state: [u8;32], row:u8, payload:*const u8, len:usize,
        answers:[[u8;32];3],
    }
    impl Digest32 for AbsorbObserver {
        fn digest(&self,parts:&[&[u8]])->[u8;32] {
            let call = unsafe { let c=CALLS; CALLS+=1; c };
            if call==0 {
                assert_eq!(parts.len(),4);
                assert_eq!(parts[0],&self.state);
                assert_eq!(parts[1],&[0,0xa0+self.row]);
                assert_eq!(parts[2],&(self.len as u32).to_le_bytes());
                assert_eq!(parts[3].len(),self.len);
                assert_eq!(parts[3].as_ptr(),self.payload);
            } else {
                assert!(call < 3);
                assert_eq!(parts.len(),2);
                assert_eq!(parts[0],&self.answers[0]);
                assert_eq!(parts[1],&[call as u8]);
            }
            self.answers[call]
        }
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn absorb() {
        let payload:[u8;2048]=kani::any();
        let len:usize=kani::any(); kani::assume(len<=2048);
        let row:u8=kani::any(); kani::assume(row<=32);
        let state:[u8;32]=kani::any();
        let answers:[[u8;32];3]=kani::any();
        let h=AbsorbObserver{state,row,payload:payload.as_ptr(),len,answers};
        unsafe {CALLS=0;}
        let mut t=Transcript{state,hash:h};
        t.absorb(row,&payload[..len]);
        assert_eq!(t.state,answers[0]);
        unsafe {assert_eq!(CALLS,1);}
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn block() {
        let payload:[u8;2048]=kani::any();
        let len:usize=kani::any(); kani::assume(len<=2048);
        let row:u8=kani::any(); kani::assume(row<=32);
        let state:[u8;32]=kani::any();
        let answers:[[u8;32];3]=kani::any();
        let h=AbsorbObserver{state,row,payload:payload.as_ptr(),len,answers};
        unsafe {CALLS=0;}
        let mut t=Transcript{state,hash:h};
        assert_eq!(t.block(row,&payload[..len]),answers[1]);
        assert_eq!(t.state,answers[2]);
        unsafe {assert_eq!(CALLS,3);}
    }
    #[derive(Clone,Copy)]
    struct NewObserver {semantic:[u8;32],answer:[u8;32]}
    impl Digest32 for NewObserver {
        fn digest(&self,parts:&[&[u8]])->[u8;32] {
            assert_eq!(parts.len(),3);
            assert_eq!(parts[0],b"UNPROVED:R1:PRIVATE-SALTED:P3");
            assert_eq!(parts[1],&[Variant::S2.tag()]);
            assert_eq!(parts[2],&self.semantic);
            unsafe {CALLS+=1;}
            self.answer
        }
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn new_transcript() {
        let semantic:[u8;32]=kani::any(); let answer:[u8;32]=kani::any();
        unsafe {CALLS=0;}
        let t=Transcript::new(NewObserver{semantic,answer},semantic,Variant::S2);
        assert_eq!(t.state,answer);
        unsafe {assert_eq!(CALLS,1);}
    }
}
'''

extra=extra[:-2]+r"""
    #[derive(Clone,Copy)]
    struct QueryObserver {state:[u8;32],payload:*const u8,len:usize,answers:[[u8;32];17]}
    impl Digest32 for QueryObserver {
        fn digest(&self,parts:&[&[u8]])->[u8;32] {
            let call=unsafe {let c=CALLS;CALLS+=1;c};
            assert!(call<17);
            if call==0 {
                assert_eq!(parts.len(),4);
                assert_eq!(parts[0],&self.state);
                assert_eq!(parts[1],&[0,0xa0+31]);
                assert_eq!(parts[2],&(self.len as u32).to_le_bytes());
                assert_eq!(parts[3].len(),self.len);
                assert_eq!(parts[3].as_ptr(),self.payload);
            } else {
                assert_eq!(parts.len(),2);
                let prior=2*((call-1)/2);
                assert_eq!(parts[0],&self.answers[prior]);
                assert_eq!(parts[1],&[if call%2==1 {1} else {2}]);
            }
            self.answers[call]
        }
    }
    #[kani::proof]
    #[kani::unwind(84)]
    fn queries() {
        let payload:[u8;2048]=kani::any();let len:usize=kani::any();kani::assume(len<=2048);
        let state:[u8;32]=kani::any();let answers:[[u8;32];17]=kani::any();
        let h=QueryObserver{state,payload:payload.as_ptr(),len,answers};
        unsafe {CALLS=0;}
        let mut t=Transcript{state,hash:h};
        let actual=t.queries(31,&payload[..len]);
        unsafe {assert_eq!(CALLS,17);}
        let blocks=core::array::from_fn(|k| answers[2*k+1]);
        let advances=core::array::from_fn(|k| answers[2*k+2]);
        match aspis_core::r0_transcript::queries_from_pairs(&blocks,&advances) {
            Ok((q,after))=>{assert!(matches!(actual,Ok(values) if values==q));assert_eq!(t.state,after);}
            Err(_)=>{assert!(matches!(actual,Err(crate::verifier::Error::Transcript)));assert_eq!(t.state,answers[0]);}
        }
    }
}
"""


a=src.index('        self.absorb(row,payload);',src.index('    pub fn queries('))
b=src.index('        let (q,state)=aspis_core::r0_transcript::queries_from_pairs',a)
prefix=src[a:b]
extra=extra[:-2]+r"""
    #[kani::proof]
    #[kani::unwind(84)]
    fn queries_prefix() {
        let backing:[u8;2048]=kani::any();let len:usize=kani::any();kani::assume(len<=2048);
        let state:[u8;32]=kani::any();let answers:[[u8;32];17]=kani::any();
        let h=QueryObserver{state,payload:backing.as_ptr(),len,answers};
        unsafe {CALLS=0;}
        let mut actual=Transcript{state,hash:h};
        let row=31;let payload=&backing[..len];
"""+prefix.replace('self.','actual.')+r"""
        unsafe {assert_eq!(CALLS,17);}
        for k in 0..8 {
            assert_eq!(blocks[k],answers[2*k+1]);
            assert_eq!(advances[k],answers[2*k+2]);
        }
        assert_eq!(state,answers[16]);
        assert_eq!(actual.state,answers[0]);
    }
}
"""
import hashlib,json
(E/'query-prefix.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(src.encode()).hexdigest(),prefix=prefix,cut_before='aspis_core::r0_transcript::queries_from_pairs',scope='literal callback-prefix cut only, not full queries method transport'),indent=2)+'\n')

(E/'rust-sources/transcript.rs').write_text(src+extra)
p=E/'harness/kani-transcript.py'
s=(E/'harness/kani.py').read_text().replace("'-p','aspis-prover'","'-p','aspis-r1-cost-probe'").replace("'--features','r0'","'--features','private-leaf-salts'")
s=s.replace("'source_hashes':", "'source_hashes':")
# The full input snapshot is collected separately; include the changed input
# in every launch's own receipt as well.
s=s.replace("list((H/'src/crates/aspis-prover/src').glob('*.rs'))", "list((H/'src/crates/aspis-r1-cost-probe/src').glob('*.rs'))+list((H/'src/crates/aspis-prover/src').glob('*.rs'))")
p.write_text(s)
