//! UNPROVED COST PROBE. Explicit opening schedule, including rho after queries.
use aspis_core::r0::CodeField;
use aspis_core::{Digest32,field::WideExact as E};
use crate::transport::Variant;
pub struct Transcript<H: Digest32> { pub state:[u8;32], hash:H }
impl<H: Digest32> Transcript<H> {
    pub fn new(hash:H, semantic_state:[u8;32], variant:Variant) -> Self {
        #[cfg(not(feature = "private-leaf-salts"))]
        let domain: &[u8] = b"UNPROVED:R1:COST-PROBE:P2";
        #[cfg(feature = "private-leaf-salts")]
        let domain: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:P3";
        Self { state:hash.digest(&[domain,&[variant.tag()],&semantic_state]), hash }
    }
    pub fn absorb(&mut self, row:u8, payload:&[u8]) {
        self.state=self.hash.digest(&[&self.state,&[0,0xa0+row],&(payload.len() as u32).to_le_bytes(),payload]);
    }
    pub fn block(&mut self,row:u8,payload:&[u8])->[u8;32] {
        self.absorb(row,payload);
        let block=self.hash.digest(&[&self.state,&[1]]);
        self.state=self.hash.digest(&[&self.state,&[2]]);
        block
    }
    pub fn scalar(&mut self,row:u8,payload:&[u8],nonzero:bool)->E {
        let block=self.block(row,payload);
        let out=if nonzero {crate::sampler::gamma_sample(&block)} else {crate::sampler::ordinary_sample(&block)};
        crate::trace::value(4,row as usize,out); out
    }
    /// Final query-residual batching: at most 22 coefficients, so a nonzero
    /// residual has at most 21 roots even when sampled from the K subfield.
    /// Gamma and both folding challenges continue to use E.
    pub fn scalar_k(&mut self,row:u8,payload:&[u8])->aspis_core::field::QM31 {
        let out=crate::sampler::qm31_sample(&self.block(row,payload));
        crate::trace::value(4,row as usize,E::from_qm31(out)); out
    }
    pub fn queries(&mut self, row:u8, payload:&[u8])->Result<[u32;22],crate::verifier::Error> {
        self.absorb(row,payload);
        let mut blocks=[[0;32];8];let mut advances=blocks; let mut state=self.state;
        blocks[0]=self.hash.digest(&[&state,&[1]]);
        advances[0]=self.hash.digest(&[&state,&[2]]);state=advances[0];
        blocks[1]=self.hash.digest(&[&state,&[1]]);
        advances[1]=self.hash.digest(&[&state,&[2]]);state=advances[1];
        blocks[2]=self.hash.digest(&[&state,&[1]]);
        advances[2]=self.hash.digest(&[&state,&[2]]);state=advances[2];
        blocks[3]=self.hash.digest(&[&state,&[1]]);
        advances[3]=self.hash.digest(&[&state,&[2]]);state=advances[3];
        blocks[4]=self.hash.digest(&[&state,&[1]]);
        advances[4]=self.hash.digest(&[&state,&[2]]);state=advances[4];
        blocks[5]=self.hash.digest(&[&state,&[1]]);
        advances[5]=self.hash.digest(&[&state,&[2]]);state=advances[5];
        blocks[6]=self.hash.digest(&[&state,&[1]]);
        advances[6]=self.hash.digest(&[&state,&[2]]);state=advances[6];
        blocks[7]=self.hash.digest(&[&state,&[1]]);
        advances[7]=self.hash.digest(&[&state,&[2]]);state=advances[7];
        let (q,state)=aspis_core::r0_transcript::queries_from_pairs(&blocks,&advances).map_err(|_|crate::verifier::Error::Transcript)?;
        self.state=state;
        { let u=q[0]; crate::trace::value(5,0,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[1]; crate::trace::value(5,1,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[2]; crate::trace::value(5,2,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[3]; crate::trace::value(5,3,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[4]; crate::trace::value(5,4,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[5]; crate::trace::value(5,5,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[6]; crate::trace::value(5,6,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[7]; crate::trace::value(5,7,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[8]; crate::trace::value(5,8,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[9]; crate::trace::value(5,9,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[10]; crate::trace::value(5,10,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[11]; crate::trace::value(5,11,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[12]; crate::trace::value(5,12,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[13]; crate::trace::value(5,13,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[14]; crate::trace::value(5,14,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[15]; crate::trace::value(5,15,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[16]; crate::trace::value(5,16,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[17]; crate::trace::value(5,17,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[18]; crate::trace::value(5,18,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[19]; crate::trace::value(5,19,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[20]; crate::trace::value(5,20,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[21]; crate::trace::value(5,21,E::from_m31(aspis_core::field::M31(u))); }
        Ok(q)
    }
}

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
    let context=StateOnlyHidingContext::pool_v1_pair_forest_v1(hash(&[&public_bytes]),mask_nonce);
    let binding=hash(&[b"UNPROVED:R1:P3:PRIVATE-ATTEMPT",&public_bytes,&[variant.tag()],&context.encode()]);

        unsafe {
            assert_eq!(CALLS,2);assert_eq!(binding,ANSWERS[1]);
            assert_eq!(context.statement_digest,ANSWERS[0]);assert_eq!(context.mask_nonce,NONCE);
        }
    }
}
