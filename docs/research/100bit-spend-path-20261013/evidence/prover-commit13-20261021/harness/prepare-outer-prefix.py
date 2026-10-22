#!/usr/bin/env python3
"""Literal secure outer prefix after public serialization, before the caller."""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
source=Path('crates/aspis-r1-cost-probe/src/prover.rs').read_text()
a=source.index('    let context=',source.index('pub fn prove_masked_attempt('))
b=source.index('    prove_masked_with_attempt(',a)
prefix=source[a:b]
assert prefix.count('attempt.mask_nonce()')==1
cut=prefix.replace('attempt.mask_nonce()','mask_nonce')
code=r'''
#[cfg(kani)]
mod outer13 {
    use super::*;
    use aspis_core::state_only_hiding::StateOnlyHidingContext;
    static mut CALLS:usize=0;
    static mut PUBLIC:*const u8=core::ptr::null();
    static mut LENGTH:usize=0;
    static mut NONCE:[u8;32]=[0;32];
    static mut ANSWERS:[[u8;32];2]=[[0;32];2];
    fn observer(parts:&[&[u8]])->[u8;32] {
        unsafe {
            let call=CALLS;CALLS+=1;assert!(call<2);
            if call==0 {
                assert_eq!(parts.len(),1);assert_eq!(parts[0].as_ptr(),PUBLIC);assert_eq!(parts[0].len(),LENGTH);
            } else {
                assert_eq!(parts.len(),4);assert_eq!(parts[0],b"UNPROVED:R1:P3:PRIVATE-ATTEMPT");
                assert_eq!(parts[1].as_ptr(),PUBLIC);assert_eq!(parts[1].len(),LENGTH);
                assert_eq!(parts[2],&[Variant::S2.tag()]);
                let expected=StateOnlyHidingContext::pool_v1_pair_forest_v1(ANSWERS[0],NONCE);
                assert_eq!(parts[3],&expected.encode());
            }
            ANSWERS[call]
        }
    }
    #[kani::proof]
    #[kani::unwind(170)]
    fn public_digest_and_binding_prefix() {
        let backing:[u8;4096]=kani::any();
        let len:usize=kani::any();kani::assume(len<=4096);
        let public_bytes=&backing[..len];let mask_nonce:[u8;32]=kani::any();
        let variant=Variant::S2;let hash:aspis_core::HashFn=observer;
        unsafe{CALLS=0;PUBLIC=backing.as_ptr();LENGTH=len;NONCE=mask_nonce;ANSWERS=kani::any();}
'''+cut+r'''
        unsafe {
            assert_eq!(CALLS,2);assert_eq!(binding,ANSWERS[1]);
            assert_eq!(context.statement_digest,ANSWERS[0]);assert_eq!(context.mask_nonce,NONCE);
        }
    }
}
'''
p=E/'rust-sources/transcript.rs'
s=p.read_text().split('\n#[cfg(kani)]\nmod outer13')[0]
(p.parent/'transcript.rs.query-v2.txt').write_text(s)
p.write_text(s+code)
(E/'outer-prefix-generation.json').write_text(json.dumps(dict(source='crates/aspis-r1-cost-probe/src/prover.rs',source_sha256=hashlib.sha256(source.encode()).hexdigest(),literal_prefix=prefix,only_replacement='attempt.mask_nonce() -> universally arbitrary mask_nonce argument',generated_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),scope='source-cut prefix only; public serialization, admitted byte image and following outer caller are not claimed'),indent=2)+'\n')
