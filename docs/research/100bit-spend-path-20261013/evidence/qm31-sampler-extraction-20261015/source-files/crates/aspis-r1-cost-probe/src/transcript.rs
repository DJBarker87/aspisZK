//! UNPROVED COST PROBE. Explicit opening schedule, including rho after queries.
use aspis_core::r0::CodeField;
use aspis_core::{HashFn,field::WideExact as E};
use crate::transport::Variant;
pub struct Transcript { pub state:[u8;32], hash:HashFn }
impl Transcript {
    pub fn new(hash:HashFn, semantic_state:[u8;32], variant:Variant) -> Self {
        #[cfg(not(feature = "private-leaf-salts"))]
        let domain: &[u8] = b"UNPROVED:R1:COST-PROBE:P2";
        #[cfg(feature = "private-leaf-salts")]
        let domain: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:P3";
        Self { state:hash(&[domain,&[variant.tag()],&semantic_state]), hash }
    }
    pub fn absorb(&mut self, row:u8, payload:&[u8]) {
        self.state=(self.hash)(&[&self.state,&[0,0xa0+row],&(payload.len() as u32).to_le_bytes(),payload]);
    }
    pub fn block(&mut self,row:u8,payload:&[u8])->[u8;32] {
        self.absorb(row,payload);
        let block=(self.hash)(&[&self.state,&[1]]);
        self.state=(self.hash)(&[&self.state,&[2]]);
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
        for k in 0..8 {
            blocks[k]=(self.hash)(&[&state,&[1]]);
            advances[k]=(self.hash)(&[&state,&[2]]);state=advances[k];
        }
        let (q,state)=aspis_core::r0_transcript::queries_from_pairs(&blocks,&advances).map_err(|_|crate::verifier::Error::Transcript)?;
        self.state=state;
        for (i,&u) in q.iter().enumerate() { crate::trace::value(5,i,E::from_m31(aspis_core::field::M31(u))); }
        Ok(q)
    }
}
