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
        let out=if nonzero {crate::host_sampler::gamma_sample(&block)} else {crate::host_sampler::ordinary_sample(&block)};
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
        let (q,state)=queries_from_pairs(&blocks,&advances)?;
        self.state=state;
        trace_queries(&q);
        Ok(q)
    }
}

fn trace_queries(q:&[u32;22]) {
    let mut i=0;
    while i<22 {crate::trace::value(5,i,E::from_m31(aspis_core::field::M31(q[i])));i+=1;}
}

/// Preserve scanOut's pre-word stop check, including the extra selected block
/// when the 22nd distinct query is the final word of a block. All eight pairs
/// have already been read by the caller, just as in the v2 transcript.
fn queries_from_pairs(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),crate::verifier::Error> {
    scan_query_words(blocks,advances,[0;22],0,0)
}

fn scan_query_words(blocks:&[[u8;32];8],advances:&[[u8;32];8],mut accepted:[u32;22],n:usize,draws:usize)->Result<([u32;22],[u8;32]),crate::verifier::Error> {
    if draws==64 {
        return if n==22 {Ok((accepted,advances[7]))} else {Err(crate::verifier::Error::Transcript)};
    }
    let k=draws/8;
    if n==22 {return Ok((accepted,advances[k]));}
    let at=4*(draws%8);
    let candidate=u32::from_le_bytes([blocks[k][at],blocks[k][at+1],blocks[k][at+2],blocks[k][at+3]])&0x3ffff;
    if query_contains(&accepted,n,candidate) {
        scan_query_words(blocks,advances,accepted,n,draws+1)
    } else {
        accepted[n]=candidate;
        scan_query_words(blocks,advances,accepted,n+1,draws+1)
    }
}
fn query_contains(accepted:&[u32;22],n:usize,candidate:u32)->bool {
    let mut i=0;
    while i<n {if accepted[i]==candidate {return true;} i+=1;}
    false
}
