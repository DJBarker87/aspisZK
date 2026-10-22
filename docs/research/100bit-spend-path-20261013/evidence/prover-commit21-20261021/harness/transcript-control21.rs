
#[cfg(any(kani,aeneas_ref))]
pub mod control21 {
use super::*;
pub trait Policy {
 fn gamma(block:&[u8;32])->E;
 fn ordinary(block:&[u8;32])->E;
 fn qm31(block:&[u8;32])->aspis_core::field::QM31;
 fn queries(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),crate::verifier::Error>;
}
pub struct Transcript<H: Digest32,P:Policy> { pub state:[u8;32], hash:H, pub trace:alloc::vec::Vec<(u16,usize,E)>, marker:core::marker::PhantomData<P> }
impl<H: Digest32,P:Policy> Transcript<H,P> {
    pub fn new(hash:H, semantic_state:[u8;32], variant:Variant) -> Self {
        #[cfg(not(feature = "private-leaf-salts"))]
        let domain: &[u8] = b"UNPROVED:R1:COST-PROBE:P2";
        #[cfg(feature = "private-leaf-salts")]
        let domain: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:P3";
        Self { state:hash.digest(&[domain,&[variant.tag()],&semantic_state]), hash, trace:alloc::vec::Vec::new(), marker:core::marker::PhantomData }
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
        let out=if nonzero {P::gamma(&block)} else {P::ordinary(&block)};
        self.trace.push((4,row as usize,out)); out
    }
    /// Final query-residual batching: at most 22 coefficients, so a nonzero
    /// residual has at most 21 roots even when sampled from the K subfield.
    /// Gamma and both folding challenges continue to use E.
    pub fn scalar_k(&mut self,row:u8,payload:&[u8])->aspis_core::field::QM31 {
        let out=P::qm31(&self.block(row,payload));
        self.trace.push((4,row as usize,E::from_qm31(out))); out
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
        let (q,state)=match P::queries(&blocks,&advances) {Ok(v)=>v,Err(e)=>return Err(e)};
        self.state=state;
        { let u=q[0]; self.trace.push((5,0,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[1]; self.trace.push((5,1,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[2]; self.trace.push((5,2,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[3]; self.trace.push((5,3,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[4]; self.trace.push((5,4,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[5]; self.trace.push((5,5,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[6]; self.trace.push((5,6,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[7]; self.trace.push((5,7,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[8]; self.trace.push((5,8,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[9]; self.trace.push((5,9,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[10]; self.trace.push((5,10,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[11]; self.trace.push((5,11,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[12]; self.trace.push((5,12,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[13]; self.trace.push((5,13,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[14]; self.trace.push((5,14,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[15]; self.trace.push((5,15,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[16]; self.trace.push((5,16,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[17]; self.trace.push((5,17,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[18]; self.trace.push((5,18,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[19]; self.trace.push((5,19,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[20]; self.trace.push((5,20,E::from_m31(aspis_core::field::M31(u)))); }
        { let u=q[21]; self.trace.push((5,21,E::from_m31(aspis_core::field::M31(u)))); }
        Ok(q)
    }
}


}
