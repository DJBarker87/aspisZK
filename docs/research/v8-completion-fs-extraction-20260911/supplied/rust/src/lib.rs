//! DRAFT_NOT_COMPILED. Dependency-free offline controls, not the Aspis verifier.
//! Canonical wire projections and a pure Merkle reference core for Aeneas/differential tests.
//! No network, no keys, no deployment and no replacement of the production verifier.

pub const P: u32 = 2_147_483_647;
pub const FIXED: usize = 697;
pub const RECORDS: usize = 22;
pub const RECORD_BYTES: usize = 621;
pub const RECORD_START: usize = 11228;
pub const FRONTIER_START: usize = 24890;
pub const MAX_FRONTIER: usize = 296;
pub type Digest = [u8;26];
pub type PairDigest = [Digest;2];

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error { Length, Canonical, Index, Guard, Frontier, Root }

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Wire<'a> {
    body: &'a [u8],
    fields: [[u32;4];FIXED],
    roots: PairDigest,
    half_frontier: usize,
}
impl<'a> Wire<'a> {
    pub fn parse(body: &'a [u8]) -> Result<Self,Error> {
        let extra = body.len().checked_sub(FRONTIER_START).ok_or(Error::Length)?;
        if extra % 52 != 0 || extra/52 > MAX_FRONTIER { return Err(Error::Length); }
        let mut fields = [[0u32;4];FIXED];
        for (i, field) in fields.iter_mut().enumerate() {
            for (j, limb) in field.iter_mut().enumerate() {
                let offset=16*i+4*j;
                let bytes: [u8;4] = body.get(offset..offset+4).ok_or(Error::Length)?
                    .try_into().map_err(|_|Error::Length)?;
                let value=u32::from_le_bytes(bytes);
                if value>=P { return Err(Error::Canonical); }
                *limb=value;
            }
        }
        let roots=[body[11152..11178].try_into().map_err(|_|Error::Length)?,
                   body[11178..11204].try_into().map_err(|_|Error::Length)?];
        Ok(Self{body,fields,roots,half_frontier:extra/2})
    }
    pub fn body(&self)->&'a [u8] { self.body }
    pub fn fields(&self)->&[[u32;4];FIXED] { &self.fields }
    pub fn roots(&self)->&PairDigest { &self.roots }
    pub fn record(&self,i:usize)->Result<&'a [u8],Error> {
        if i>=RECORDS { return Err(Error::Index); }
        self.body.get(RECORD_START+i*RECORD_BYTES..RECORD_START+(i+1)*RECORD_BYTES)
            .ok_or(Error::Length)
    }
    pub fn frontier(&self,phase:usize)->Result<&'a [u8],Error> {
        if phase>=2 {return Err(Error::Index);}
        let start=FRONTIER_START+phase*self.half_frontier;
        self.body.get(start..start+self.half_frontier).ok_or(Error::Length)
    }
}

/// Bit-level reference decoder. Four-u64 optimisations need a separate equivalence proof.
pub fn unpack31(bytes:&[u8], count:usize)->Result<Vec<u32>,Error> {
    if count.checked_mul(31)!=bytes.len().checked_mul(8) {return Err(Error::Length);}
    let mut result=Vec::with_capacity(count);
    for i in 0..count {
        let mut value=0u32;
        for bit in 0..31 {
            let offset=i*31+bit;
            let b=(bytes[offset/8]>>(offset%8))&1;
            value|=u32::from(b)<<bit;
        }
        if value>=P {return Err(Error::Canonical);}
        result.push(value);
    }
    Ok(result)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry { pub position:u32, pub digest:PairDigest }

/// The caller provides the actual hash operation. This trait does not declare it random.
pub trait ParentHash { fn parent(&mut self,left:&Digest,right:&Digest)->Digest; }

/// Iterative reference matching the two-tree source control flow. Returns the
/// actual computed roots; caller compares them. Source equivalence remains open.
pub fn merge<H:ParentHash>(hash:&mut H, depth:u32, entries:&[Entry],
                           frontier:&[PairDigest])->Result<PairDigest,Error> {
    if entries.is_empty() || depth>=32 {return Err(Error::Guard);}
    for pair in entries.windows(2) {
        if pair[0].position>=pair[1].position {return Err(Error::Guard);}
    }
    if entries.last().ok_or(Error::Guard)?.position >= (1u32<<depth) {return Err(Error::Guard);}
    let mut level=entries.to_vec(); let mut next=Vec::new();let mut node_pos=0;
    for _ in 0..depth {
        next.clear();let mut i=0;
        while i<level.len() {
            let current=&level[i];let position=current.position;
            let mut parent=[[0u8;26];2];
            if position&1==0 && i+1<level.len() && level[i+1].position==position+1 {
                for side in 0..2 {parent[side]=hash.parent(&current.digest[side],&level[i+1].digest[side]);}
                i+=2;
            } else {
                let sibling=frontier.get(node_pos).ok_or(Error::Frontier)?;
                node_pos+=1;
                for side in 0..2 {
                    parent[side]=if position&1==0 {hash.parent(&current.digest[side],&sibling[side])}
                        else {hash.parent(&sibling[side],&current.digest[side])};
                }
                i+=1;
            }
            next.push(Entry{position:position>>1,digest:parent});
        }
        std::mem::swap(&mut level,&mut next);
    }
    if node_pos!=frontier.len() || level.len()!=1 || level[0].position!=0 {return Err(Error::Root);}
    Ok(level[0].digest)
}

#[derive(Clone,Debug,PartialEq,Eq)]
pub struct HashReceipt {pub parts:Vec<Vec<u8>>,pub output:[u8;32]}

/// Evidence-only wrapper: records EXACT hashv slice bytes; adds no role/domain bytes.
/// Prove this wrapper's output noninterference before trusting instrumented traces.
pub struct Recorder<H> { hash:H, pub receipts:Vec<HashReceipt> }
impl<H:FnMut(&[&[u8]])->[u8;32]> Recorder<H> {
    pub fn new(hash:H)->Self {Self{hash,receipts:Vec::new()}}
    pub fn hash_parts(&mut self,parts:&[&[u8]])->[u8;32] {
        let output=(self.hash)(parts);
        self.receipts.push(HashReceipt{parts:parts.iter().map(|p|p.to_vec()).collect(),output});
        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn all_lengths() {
        for c in 0..=296 {let body=vec![0u8;24890+52*c];let w=Wire::parse(&body).unwrap();
            assert_eq!(w.frontier(0).unwrap().len(),26*c); assert_eq!(w.record(21).unwrap().len(),621);}
    }
    #[test] fn semantic_mutation_is_not_silent() {
        let a=vec![0u8;24890];let mut b=a.clone();b[16]=1;
        let wa=Wire::parse(&a).unwrap();let wb=Wire::parse(&b).unwrap();
        assert_eq!(wa.roots(),wb.roots()); assert_ne!(wa.fields(),wb.fields());
    }
    #[test] fn reject_noncanonical() {
        let mut a=vec![0u8;24890];a[..4].copy_from_slice(&P.to_le_bytes());
        assert_eq!(Wire::parse(&a),Err(Error::Canonical));
    }
    #[test] fn bit_parser_boundaries() {
        assert_eq!(unpack31(&vec![0;403],104).unwrap().len(),104);
        assert_eq!(unpack31(&vec![255;403],104),Err(Error::Canonical));
    }
    #[test] fn log_preserves_raw_parts() {
        let mut r=Recorder::new(|parts:&[&[u8]]|{let mut o=[0u8;32];o[0]=parts.iter().map(|p|p.len()).sum::<usize>() as u8;o});
        assert_eq!(r.hash_parts(&[b"a",b"bc"])[0],3);
        assert_eq!(r.receipts[0].parts,vec![b"a".to_vec(),b"bc".to_vec()]);
    }
}
