#!/usr/bin/env python3
"""Actual seed call sites around explicit material/scalar callee cuts."""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
p=E/'rust-sources/state_only_hiding.rs'
s=p.read_text().split('\n#[cfg(kani)]\npub(crate) fn empty_material13')[0]
s+='''
#[cfg(kani)]
pub(crate) fn empty_material13(mask_nonce:[u8;32]) -> StateOnlyMaskMaterial {
    StateOnlyMaskMaterial {c1:Vec::new(),mask_only_c1:core::array::from_fn(|_|Vec::new()),
        g:Vec::new(),h1_padding:Vec::new(),mask_nonce}
}
'''
p.write_text(s)
p=E/'rust-sources/state_only_entropy.rs'
s=p.read_text().split('\n#[cfg(kani)]\nmod seeds13')[0]
code=r'''
#[cfg(kani)]
mod seeds13 {
    use super::*;
    static mut CTX:StateOnlyHidingContext=StateOnlyHidingContext{
        statement_digest:[0;32],mask_nonce:[0;32],mask_layout_fingerprint:0,layout_factor_fingerprint:0};
    static mut BIND:[u8;32]=[0;32];
    static mut ENTROPY:[u8;32]=[0;32];
    static mut LEAF:[u8;32]=[0;32];
    static mut ANSWERS:[[u8;32];2]=[[0;32];2];
    static mut HASH_CALLS:usize=0;
    static mut NONCE_CALLS:usize=0;
    static mut MATERIAL_CALLS:usize=0;
    static mut SCALAR_CALLS:usize=0;
    static mut MATERIAL_OK:bool=false;
    static mut CONSUME:bool=false;
    static mut D_MODE:bool=false;
    fn observe_hash(parts:&[&[u8]])->[u8;32] {
        unsafe {
            let call=HASH_CALLS;HASH_CALLS+=1;
            assert!(call<2);
            let context=CTX;
            if !D_MODE {
                assert_eq!(call,0);assert_eq!(parts.len(),4);
                assert_eq!(parts[0],POOL_V1_SOURCE_SEED_DOMAIN);
                assert_eq!(parts[1],&BIND);assert_eq!(parts[2],&context.encode());
                assert_eq!(parts[3],&ENTROPY);
            } else if call==0 {
                assert_eq!(parts.len(),4);assert_eq!(parts[0],POOL_V1_PRIVATE_ATTEMPT_BINDING_DOMAIN);
                assert_eq!(parts[1],&BIND);assert_eq!(parts[2],&context.encode());
                assert_eq!(parts[3],POOL_V1_PRIVATE_WIRE_DESCRIPTOR);
            } else {
                assert_eq!(parts.len(),3);assert_eq!(parts[0],POOL_V1_D_SEED_DOMAIN);
                assert_eq!(parts[1],&ANSWERS[0]);assert_eq!(parts[2],&ENTROPY);
            }
            ANSWERS[call]
        }
    }
    struct Nonce {allow:bool}
    impl StateOnlyMaskNonceStore for Nonce {
        fn reserve(&mut self,d:[u8;32],n:[u8;32])->bool {
            unsafe {NONCE_CALLS+=1;assert_eq!(d,CTX.statement_digest);assert_eq!(n,CTX.mask_nonce);}
            self.allow
        }
    }
    fn material(_:HashFn,bind:[u8;32],context:StateOnlyHidingContext,
        entropy:&[u8;32],nonce:&mut impl StateOnlyMaskNonceStore)->Result<StateOnlyMaskMaterial,StateOnlyMaskBuildError> {
        unsafe {
            MATERIAL_CALLS+=1;assert_eq!(bind,BIND);assert_eq!(context,CTX);assert_eq!(entropy,&ENTROPY);
            if CONSUME {assert!(nonce.reserve(context.statement_digest,context.mask_nonce));}
            if MATERIAL_OK {Ok(crate::state_only_hiding::empty_material13(context.mask_nonce))}
            else {Err(StateOnlyMaskBuildError::MaskSampleExhausted)}
        }
    }
    fn first_scalar(expander:&mut Profile21SourceExpander)->Result<aspis_core::field::QM31,StateOnlyMaskBuildError> {
        unsafe {
            SCALAR_CALLS+=1;assert_eq!(HASH_CALLS,2);assert_eq!(*expander.seed,ANSWERS[1]);
            assert_eq!(expander.counter,0);assert_eq!(expander.word,8);assert_eq!(expander.block,[0;32]);
        }
        Err(StateOnlyMaskBuildError::MaskSampleExhausted)
    }
    fn init() -> StateOnlyHidingContext {
        let context=StateOnlyHidingContext::pool_v1_pair_forest_v1(kani::any(),kani::any());
        unsafe {
            CTX=context;BIND=kani::any();ENTROPY=kani::any();LEAF=kani::any();ANSWERS=kani::any();
            HASH_CALLS=0;NONCE_CALLS=0;MATERIAL_CALLS=0;SCALAR_CALLS=0;
            MATERIAL_OK=kani::any();CONSUME=kani::any();D_MODE=false;
        }
        context
    }
    fn source_seed_case<const CASE:usize>() {
        let context=init();
        let allow=CASE!=1;
        unsafe {
            if CASE==0 {MATERIAL_OK=true;CONSUME=true;}
            if CASE==2 {MATERIAL_OK=false;}
            if CASE==3 {MATERIAL_OK=true;CONSUME=false;}
        }
        let attempt=unsafe {StateOnlyAttemptSecrets{mask_nonce:context.mask_nonce,
            field_mask_entropy:Zeroizing::new(ENTROPY),leaf_salt_seed:Zeroizing::new(LEAF)}};
        let mut nonce=Nonce{allow};
        let result=attempt.reserve_and_build_pool_v1_pair_forest_mask_material_v1(observe_hash,unsafe{BIND},context,&mut nonce);
        unsafe {
            assert_eq!(NONCE_CALLS,1);
            assert_eq!(MATERIAL_CALLS,usize::from(allow));
            if allow && MATERIAL_OK && CONSUME {
                let (reserved,material)=result.unwrap();
                assert_eq!(HASH_CALLS,1);assert_eq!(*reserved.source_mask_seed,ANSWERS[0]);
                assert_eq!(*reserved.leaf_salt_seed,LEAF);assert_eq!(reserved.mask_nonce,context.mask_nonce);
                assert_eq!(reserved.reserved_context,context);assert_eq!(reserved.precommit_binding,BIND);
                assert_eq!(material.mask_nonce,context.mask_nonce);
            } else {assert!(result.is_err());assert_eq!(HASH_CALLS,0);}
        }
    }
    #[kani::proof]
    #[kani::unwind(170)]
    #[kani::stub(crate::state_only_hiding::build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref,material)]
    fn source_seed_success() {source_seed_case::<0>();}
    #[kani::proof]
    #[kani::unwind(170)]
    #[kani::stub(crate::state_only_hiding::build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref,material)]
    fn source_seed_nonce_rejected() {source_seed_case::<1>();}
    #[kani::proof]
    #[kani::unwind(170)]
    #[kani::stub(crate::state_only_hiding::build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref,material)]
    fn source_seed_material_error() {source_seed_case::<2>();}
    #[kani::proof]
    #[kani::unwind(170)]
    #[kani::stub(crate::state_only_hiding::build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref,material)]
    fn source_seed_unconsumed() {source_seed_case::<3>();}
    #[kani::proof]
    #[kani::unwind(170)]
    #[kani::stub(Profile21SourceExpander::qm31,first_scalar)]
    fn d_seed_before_first_scalar() {
        let context=init();unsafe{D_MODE=true;}
        let reserved=unsafe{ReservedStateOnlyAttemptSecrets{mask_nonce:context.mask_nonce,
            precommit_binding:BIND,reserved_context:context,leaf_salt_seed:Zeroizing::new(LEAF),
            source_mask_seed:Zeroizing::new(ENTROPY)}};
        let masks:[u16;64]=kani::any();
        let result=reserved.derive_pool_v1_zero_factor_d(observe_hash,context,context.layout_factor_fingerprint,&masks);
        assert_eq!(result,Err(StateOnlyMaskBuildError::MaskSampleExhausted));
        unsafe{assert_eq!(HASH_CALLS,2);assert_eq!(SCALAR_CALLS,1);}
    }
}
'''
p.write_text(s+code)
(E/'seed-generation.json').write_text(json.dumps({f:hashlib.sha256((E/'rust-sources'/f).read_bytes()).hexdigest() for f in ['state_only_hiding.rs','state_only_entropy.rs']},indent=2)+'\n')
