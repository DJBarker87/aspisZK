//! SPEC §9 P1 proof records. Every width is fixed, including the 22 paths.
//! Records: beforeZ1, values, scalar, poly(six), final, opening. Claims and
//! roots come from the trusted semantic boundary, not redundant proof fields.
use super::{
    merkle::{self, Path},
    opening::Endpoints,
    Error, FinalMessage,
};
use crate::{field::WideExact as E, HashFn};
use alloc::vec::Vec;
pub const E_BYTES: usize = 32;
pub const FIBRE_VALUE_BYTES: usize = 4 * (26 * 4 + 3 * 16);
pub const PATH_BYTES: usize = 6 * 7 * 32;
pub const FIBRE_BYTES: usize = FIBRE_VALUE_BYTES + 2 * PATH_BYTES;
pub const PROOF_BYTES: usize = 6 * 5 + (29 + 58 + 1 + 6 + 256) * 32 + 22 * FIBRE_BYTES;
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FibreOpening {
    pub values: [[E; 29]; 4],
    pub paths: [Path; 2],
}
impl FibreOpening {
    pub(crate) fn empty() -> Self {
        Self {
            values: [[E::ZERO; 29]; 4],
            paths: [[[[0; 32]; 7]; 6]; 2],
        }
    }
    pub fn leaf_hashes(&self, hash: HashFn) -> Result<[[u8; 32]; 2], Error> {
        let mut c1 = [0u8; 480];
        let mut c2 = [0u8; 128];
        let mut a = 0;
        let mut b = 0;
        for s in 0..4 {
            for l in 0..29 {
                let bytes = lane_bytes(self.values[s][l], l)?;
                let width = if l < 26 { 4 } else { 16 };
                if l == 26 || l == 27 {
                    c2[b..b + width].copy_from_slice(&bytes[..width]);
                    b += width;
                } else {
                    c1[a..a + width].copy_from_slice(&bytes[..width]);
                    a += width;
                }
            }
        }
        Ok([
            merkle::leaf(hash, merkle::C1_TAG, &c1),
            merkle::leaf(hash, merkle::C2_TAG, &c2),
        ])
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpeningProof {
    /// Kept separately: §9 explicitly does not impose equality with y[*][0].
    pub y0: [E; 29],
    pub y: Endpoints,
    pub v: E,
    pub coefficients: [E; 6],
    pub final_message: FinalMessage<E>,
    pub openings: Vec<FibreOpening>,
}
fn lane_bytes(value: E, lane: usize) -> Result<[u8; 32], Error> {
    if value.to_limbs()[if lane < 26 { 1 } else { 4 }..]
        .iter()
        .any(|&x| x != 0)
    {
        return Err(Error::WrongField);
    }
    Ok(value.to_le_bytes())
}
struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], Error> {
        let end = self.at.checked_add(n).ok_or(Error::Parse)?;
        let result = self.bytes.get(self.at..end).ok_or(Error::Parse)?;
        self.at = end;
        Ok(result)
    }
    fn record(&mut self, tag: u8, len: usize) -> Result<(), Error> {
        let header = self.take(5)?;
        if header[0] != tag
            || u32::from_le_bytes([header[1], header[2], header[3], header[4]]) as usize != len
        {
            return Err(Error::Parse);
        }
        Ok(())
    }
    fn field(&mut self, width: usize) -> Result<E, Error> {
        let mut bytes = [0u8; 32];
        bytes[..width].copy_from_slice(self.take(width)?);
        E::from_le_bytes(&bytes).ok_or(Error::NonCanonical)
    }
    fn fields<const N: usize>(&mut self) -> Result<[E; N], Error> {
        let mut out = [E::ZERO; N];
        for x in &mut out {
            *x = self.field(32)?;
        }
        Ok(out)
    }
}
impl OpeningProof {
    pub fn parse(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() != PROOF_BYTES {
            return Err(Error::Parse);
        }
        let mut r = Reader { bytes, at: 0 };
        r.record(5, 29 * 32)?;
        let y0 = r.fields()?;
        r.record(6, 58 * 32)?;
        let mut y = [[E::ZERO; 2]; 29];
        for pair in &mut y {
            *pair = r.fields()?;
        }
        r.record(7, 32)?;
        let v = r.field(32)?;
        r.record(9, 6 * 32)?;
        let coefficients = r.fields()?;
        r.record(10, 256 * 32)?;
        let final_message = r.fields()?;
        r.record(11, 22 * FIBRE_BYTES)?;
        let mut openings = Vec::new();
        openings
            .try_reserve_exact(22)
            .map_err(|_| Error::Allocation)?;
        for _ in 0..22 {
            let mut opening = FibreOpening::empty();
            for slot in &mut opening.values {
                for (l, x) in slot.iter_mut().enumerate() {
                    *x = r.field(if l < 26 { 4 } else { 16 })?;
                }
            }
            for path in &mut opening.paths {
                for level in path {
                    for node in level {
                        node.copy_from_slice(r.take(32)?);
                    }
                }
            }
            openings.push(opening);
        }
        if r.at != bytes.len() {
            return Err(Error::Parse);
        }
        Ok(Self {
            y0,
            y,
            v,
            coefficients,
            final_message,
            openings,
        })
    }
    pub fn encode(&self) -> Result<Vec<u8>, Error> {
        if self.openings.len() != 22 {
            return Err(Error::WrongLength);
        }
        let mut out = Vec::new();
        out.try_reserve_exact(PROOF_BYTES)
            .map_err(|_| Error::Allocation)?;
        fn header(out: &mut Vec<u8>, tag: u8, len: usize) {
            out.push(tag);
            out.extend_from_slice(&(len as u32).to_le_bytes());
        }
        header(&mut out, 5, 29 * 32);
        for x in self.y0 {
            out.extend_from_slice(&x.to_le_bytes());
        }
        header(&mut out, 6, 58 * 32);
        for pair in self.y {
            for x in pair {
                out.extend_from_slice(&x.to_le_bytes());
            }
        }
        header(&mut out, 7, 32);
        out.extend_from_slice(&self.v.to_le_bytes());
        header(&mut out, 9, 6 * 32);
        for x in self.coefficients {
            out.extend_from_slice(&x.to_le_bytes());
        }
        header(&mut out, 10, 256 * 32);
        for x in self.final_message {
            out.extend_from_slice(&x.to_le_bytes());
        }
        header(&mut out, 11, 22 * FIBRE_BYTES);
        for opening in &self.openings {
            for slot in opening.values {
                for (l, x) in slot.iter().enumerate() {
                    out.extend_from_slice(&lane_bytes(*x, l)?[..if l < 26 { 4 } else { 16 }]);
                }
            }
            for path in opening.paths {
                for level in path {
                    for node in level {
                        out.extend_from_slice(&node);
                    }
                }
            }
        }
        Ok(out)
    }
}

/// Verifier view of P1. Canonicality is checked for every scalar up front,
/// exactly as OpeningProof::parse; values and authentication paths stay in
/// the input account. No decoded 256/1024-element array is returned by value.
pub struct OpeningView<'a> {
    pub y0: &'a [u8],
    pub y: &'a [u8],
    pub v: E,
    pub coefficients: [E; 6],
    pub final_message: &'a [u8],
    openings: &'a [u8],
}
impl<'a> OpeningView<'a> {
    pub fn parse(bytes: &'a [u8]) -> Result<Self, Error> {
        if bytes.len()!=PROOF_BYTES {return Err(Error::Parse);}
        let mut r=Reader{bytes,at:0};
        fn canonical<'b>(r:&mut Reader<'b>, count:usize) -> Result<&'b [u8],Error> {
            let start=r.at;
            for _ in 0..count {r.field(32)?;}
            Ok(&r.bytes[start..r.at])
        }
        r.record(5,29*32)?; let y0=canonical(&mut r,29)?;
        r.record(6,58*32)?; let y=canonical(&mut r,58)?;
        r.record(7,32)?;let v=r.field(32)?;
        r.record(9,6*32)?;let coefficients=r.fields()?;
        r.record(10,256*32)?;let final_message=canonical(&mut r,256)?;
        r.record(11,22*FIBRE_BYTES)?;
        let start=r.at;
        for _ in 0..22 {
            for _ in 0..4 {for l in 0..29 {r.field(if l<26 {4}else{16})?;}}
            r.take(2*PATH_BYTES)?;
        }
        if r.at!=bytes.len(){return Err(Error::Parse);}
        Ok(Self{y0,y,v,coefficients,final_message,openings:&bytes[start..]})
    }
    pub fn opening_count(&self)->usize {self.openings.len()/FIBRE_BYTES}
    pub fn endpoint(&self,lane:usize,point:usize)->E {canonical_e(self.y,2*lane+point)}
    pub fn final_coefficient(&self,j:usize)->E {canonical_e(self.final_message,j)}
    pub fn fibre(&self,i:usize)->FibreView<'a> {
        FibreView{bytes:&self.openings[i*FIBRE_BYTES..(i+1)*FIBRE_BYTES]}
    }
}
fn canonical_e(bytes:&[u8],i:usize)->E {
    E::from_le_bytes(&bytes[32*i..32*(i+1)]).expect("canonical P1 view")
}
pub struct FibreView<'a>{bytes:&'a [u8]}
impl FibreView<'_> {
    pub fn value(&self,slot:usize,lane:usize)->E {
        let start=slot*152+if lane<26 {lane*4}else{104+(lane-26)*16};
        let n=if lane<26 {4}else{16};
        let mut b=[0;32];b[..n].copy_from_slice(&self.bytes[start..start+n]);
        E::from_le_bytes(&b).expect("canonical P1 fibre")
    }
    pub fn leaf_hashes(&self,hash:HashFn)->Result<[[u8;32];2],Error>{
        let mut c1=[0;480];let mut c2=[0;128];let(mut a,mut b)=(0,0);
        // Preserve the existing leaf layout and lane field check.
        for s in 0..4 {for l in 0..29 {
            let bytes=lane_bytes(self.value(s,l),l)?;let n=if l<26 {4}else{16};
            if l==26 || l==27 {c2[b..b+n].copy_from_slice(&bytes[..n]);b+=n;}
            else {c1[a..a+n].copy_from_slice(&bytes[..n]);a+=n;}
        }}
        Ok([merkle::leaf(hash,merkle::C1_TAG,&c1),merkle::leaf(hash,merkle::C2_TAG,&c2)])
    }
    pub fn paths(&self)->&[Path;2] {
        let bytes=&self.bytes[FIBRE_VALUE_BYTES..];
        // Path is nested u8 arrays (alignment 1), with exactly this size.
        unsafe {&*(bytes.as_ptr() as *const [Path;2])}
    }
}
