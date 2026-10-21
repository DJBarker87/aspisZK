#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
s=Path('crates/aspis-r1-cost-probe/src/transcript.rs').read_text()
code=r'''
#[cfg(kani)]
mod query13 {
    use super::*;
    static mut CALLS:usize=0;
    static mut SAMPLER_CALLS:usize=0;
    static mut ANSWERS:[[u8;32];17]=[[0;32];17];
    static mut QUERIES:[u32;22]=[0;22];
    static mut SELECTED:[u8;32]=[0;32];
    static mut SUCCESS:bool=false;
    #[derive(Clone,Copy)]
    struct Observer {state:[u8;32],payload:*const u8,len:usize}
    impl Digest32 for Observer {
        fn digest(&self,parts:&[&[u8]])->[u8;32] {
            let call=unsafe{let c=CALLS;CALLS+=1;c};
            assert!(call<17);
            if call==0 {
                assert_eq!(parts.len(),4);
                assert_eq!(parts[0],&self.state);
                assert_eq!(parts[1],&[0,0xbf]);
                assert_eq!(parts[2],&(self.len as u32).to_le_bytes());
                assert_eq!(parts[3].as_ptr(),self.payload);
                assert_eq!(parts[3].len(),self.len);
            } else {
                assert_eq!(parts.len(),2);
                let prior=2*((call-1)/2);
                unsafe{assert_eq!(parts[0],&ANSWERS[prior]);}
                assert_eq!(parts[1],&[if call%2==1 {1}else{2}]);
            }
            unsafe{ANSWERS[call]}
        }
    }
    // Universal callee-result observer: no claim to implement the sampler.
    // Proves the full caller's transport for every possible sampler outcome.
    fn sampler(blocks:&[[u8;32];8],advances:&[[u8;32];8])
      ->Result<([u32;22],[u8;32]),aspis_core::transcript::QuerySampleError> {
        unsafe {
            assert_eq!(CALLS,17);
            SAMPLER_CALLS+=1;
            for k in 0..8 {
                assert_eq!(blocks[k],ANSWERS[2*k+1]);
                assert_eq!(advances[k],ANSWERS[2*k+2]);
            }
            if SUCCESS {Ok((QUERIES,SELECTED))}
            else {Err(aspis_core::transcript::QuerySampleError::DrawLimitExhausted{accepted:0,max_draws:64})}
        }
    }
    #[kani::proof]
    #[kani::unwind(170)]
    #[kani::stub(aspis_core::r0_transcript::queries_from_pairs,sampler)]
    fn result_and_retained_state() {
        let payload:[u8;2048]=kani::any();
        let len:usize=kani::any();kani::assume(len<=2048);
        let state:[u8;32]=kani::any();
        unsafe{
            CALLS=0;SAMPLER_CALLS=0;ANSWERS=kani::any();QUERIES=kani::any();
            SELECTED=kani::any();SUCCESS=kani::any();
        }
        let h=Observer{state,payload:payload.as_ptr(),len};
        let mut t=Transcript{state,hash:h};
        let actual=t.queries(31,&payload[..len]);
        unsafe {
            assert_eq!(CALLS,17);assert_eq!(SAMPLER_CALLS,1);
            if SUCCESS {assert_eq!(actual,Ok(QUERIES));assert_eq!(t.state,SELECTED);}
            else {assert_eq!(actual,Err(crate::verifier::Error::Transcript));assert_eq!(t.state,ANSWERS[0]);}
        }
    }
}
'''
p=E/'rust-sources/transcript.rs';p.write_text(s+code)
(E/'query-generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(s.encode()).hexdigest(),generated_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),boundary='queries_from_pairs: arbitrary result, exact input arrays, all outer calls and retained caller state'),indent=2)+'\n')
p=E/'harness/kani-transcript.py'
s=(E/'harness/kani.py').read_text().replace('rust-worker.lock','transcript-worker.lock').replace("'-p','aspis-prover'","'-p','aspis-r1-cost-probe'").replace("'--features','r0'","'--features','private-leaf-salts'").replace("list((H/'src/crates/aspis-prover/src').glob('*.rs'))", "list((H/'src/crates/aspis-r1-cost-probe/src').glob('*.rs'))+list((H/'src/crates/aspis-prover/src').glob('*.rs'))")
p.write_text(s)
