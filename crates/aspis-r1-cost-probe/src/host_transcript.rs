//! Host-only counted opening transcript and ordered query scanner.
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
        let mut k=0;
        while k<8 {
            blocks[k]=self.hash.digest(&[&state,&[1]]);
            advances[k]=self.hash.digest(&[&state,&[2]]);
            state=advances[k];
            k+=1;
        }
        let (q,state)=queries_from_pairs(&blocks,&advances)?;
        self.state=state;
        let mut i=0;
        while i<22 {crate::trace::value(5,i,E::from_m31(aspis_core::field::M31(q[i])));i+=1;}
        Ok(q)
    }
}

/// Preserve scanOut's pre-word stop check, including the extra selected block
/// when the 22nd distinct query is the final word of a block. All eight pairs
/// have already been read by the caller, just as in the v2 transcript.
fn queries_from_pairs(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),crate::verifier::Error> {
    let mut accepted=[0u32;22];
    let mut n=0;
    let mut draws=0;
    let mut k=0;
    while k<8 {
        let mut word=0;
        while word<8 {
            if n==22 || draws==64 {return Ok((accepted,advances[k]));}
            let at=4*word;
            let candidate=u32::from_le_bytes([blocks[k][at],blocks[k][at+1],blocks[k][at+2],blocks[k][at+3]])&0x3ffff;
            draws+=1;
            let mut found=false;
            let mut i=0;
            while i<n {
                if accepted[i]==candidate {found=true;break;}
                i+=1;
            }
            if !found {accepted[n]=candidate;n+=1;}
            word+=1;
        }
        k+=1;
    }
    if n==22 {Ok((accepted,advances[7]))} else {Err(crate::verifier::Error::Transcript)}
}
