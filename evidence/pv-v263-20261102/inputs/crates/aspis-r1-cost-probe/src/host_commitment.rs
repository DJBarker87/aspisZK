//! UNPROVED COST PROBE. Isolated packed commitments and native encoder.
use alloc::vec::Vec;
use aspis_core::{HashFn,field::{WideExact as E,M31,QM31},r0::{domain::{self,FibreIndex,Point},fold,merkle,wire::FibreOpening,opening::LANES,heap::filled,CodeField,Error,Message,FIBRE_COUNT,WORD_LEN}};
/// Natural-product evaluation tree. Coordinates are always in F.
pub struct EncodingDomain {
    xy: Vec<Point<M31>>,
    levels: Vec<Vec<M31>>,
}
impl EncodingDomain {
    pub fn new() -> Result<Self, Error> {
        let xy=domain_points()?;
        let mut levels=Vec::new();
        levels.try_reserve_exact(9).map_err(|_|Error::Allocation)?;
        let first=domain_first_level(&xy)?;
        levels.push(first);
        let levels=domain_append_levels(levels,0)?;
        Ok(Self{xy,levels})
    }
    pub fn evaluate<T: CodeField>(&self,coefficients:&[T],depth:usize)->Result<Vec<T>,Error> {
        let count=self.levels[depth].len();
        if coefficients.len()==1 {return filled(count,coefficients[0]);}
        let (even,odd)=split_coefficients(coefficients)?;
        let a=self.evaluate(&even,depth+1)?;
        let b=self.evaluate(&odd,depth+1)?;
        merge_evaluations(&self.levels[depth],&a,&b)
    }
    /// Exact §3 encoder at every stored index, O(N log 1024), using
    /// N_(2j)(x)=N_j(2x²−1), N_(2j+1)(x)=x*N_j(2x²−1).
    pub fn encode<T: CodeField>(&self, message: &Message<T>) -> Result<Vec<T>, Error> {
        let mut channels = Vec::new();
        channels
            .try_reserve_exact(4)
            .map_err(|_| Error::Allocation)?;
        let first=self.encode_channel(message,0)?;channels.push(first);
        let second=self.encode_channel(message,1)?;channels.push(second);
        let third=self.encode_channel(message,2)?;channels.push(third);
        let fourth=self.encode_channel(message,3)?;channels.push(fourth);
        let mut word=filled(WORD_LEN,T::ZERO)?;
        let count=self.xy.len();let mut u=0;
        while u<count {
            let values=encode_fibre(self.xy[u],&channels,u);
            word[4*u..4*u+4].copy_from_slice(&values);u+=1;
        }
        Ok(word)
    }
    fn encode_channel<T:CodeField>(&self,message:&Message<T>,s:usize)->Result<Vec<T>,Error> {
        let mut coefficients=[T::ZERO;256];let mut d=0;
        while d<256 {let value=message[4*d+s];coefficients[d]=value;d+=1;}
        self.evaluate(&coefficients,0)
    }

}

fn encode_fibre<T:CodeField>(point:Point<M31>,channels:&[Vec<T>],u:usize)->[T;4] {
    let x=T::from_m31(point.x);let y=T::from_m31(point.y);
    let values=[channels[0][u],channels[1][u],channels[2][u],channels[3][u]];
    fold::phi_inverse(x,y,values)
}

fn split_coefficients<T:CodeField>(coefficients:&[T])->Result<(Vec<T>,Vec<T>),Error> {
    let mut even=filled(coefficients.len()/2,T::ZERO)?;
    let mut odd=filled(even.len(),T::ZERO)?;
    let mut j=0;
    while j<even.len() {even[j]=coefficients[2*j];odd[j]=coefficients[2*j+1];j+=1;}
    Ok((even,odd))
}
fn merge_evaluations<T:CodeField>(nodes:&[M31],a:&[T],b:&[T])->Result<Vec<T>,Error> {
    let mut out=filled(nodes.len(),T::ZERO)?;let mut j=0;
    while j<nodes.len() {out[j]=a[j/2].add(T::from_m31(nodes[j]).mul(b[j/2]));j+=1;}
    Ok(out)
}

fn domain_points()->Result<Vec<Point<M31>>,Error> {
    let count=FIBRE_COUNT;
    let mut xy=filled(count,Point{x:M31::ZERO,y:M31::ZERO})?;
    let mut u=0;
    while u<count {xy[u]=domain::fibre_point(FibreIndex::new(u)?);u+=1;}
    Ok(xy)
}
fn domain_first_level(xy:&[Point<M31>])->Result<Vec<M31>,Error> {
    let count=FIBRE_COUNT;

    let mut first=filled(FIBRE_COUNT,M31::ZERO)?;
    let mut u=0;
    while u<count {first[u]=xy[u].x.mul(xy[u].x).double().sub(M31::ONE);u+=1;}
    Ok(first)
}
fn domain_next_level(previous:&[M31])->Result<Vec<M31>,Error> {
    let mut next=filled(previous.len()/2,M31::ZERO)?;
    let mut j=0;
    while j<next.len() {next[j]=previous[2*j].mul(previous[2*j]).double().sub(M31::ONE);j+=1;}
    Ok(next)
}
/// Structural recursion moves the level owner; no level loan crosses a loop join.
fn domain_append_levels(mut levels:Vec<Vec<M31>>,depth:usize)->Result<Vec<Vec<M31>>,Error> {
    if depth==8 {return Ok(levels);}
    let next=domain_next_level(&levels[depth])?;
    levels.push(next);
    domain_append_levels(levels,depth+1)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommitmentTime {
    C1,
    C2,
}
enum Word {
    Base(Vec<M31>),
    Secure(Vec<QM31>),
}
impl Word {
    fn value(&self, i: usize) -> E {
        match self {
            Self::Base(w) => E::from_m31(w[i]),
            Self::Secure(w) => E::from_qm31(w[i]),
        }
    }
}
/// C1 can be constructed before λ/χ; C2 separately after them. The 29-entry
/// input permits virtual lanes but only this time's lanes are committed.
pub struct Commitment {
    time: CommitmentTime,
    lanes: Vec<usize>,
    words: Vec<Word>,
    /// Binary tree of the adopted format (PREREG-PROOF-SIZE-2). The eight-way
    /// tree is retired: a prover build cannot emit an eight-way proof.
    tree: crate::host_tree::BinaryTree,
    private_salts: Option<PrivateSalts>,
}
/// Host-only secret salts retained until queried openings have been emitted.
/// Drop overwrites the full salt buffer so salts for unopened leaves are not
/// left in the allocator after proof construction.
pub struct PrivateSalts(Vec<[u8; 32]>);
impl PrivateSalts {
    pub fn new(values: Vec<[u8; 32]>) -> Self { Self(values) }
    pub fn get(&self, index: usize) -> &[u8; 32] { &self.0[index] }
    fn len(&self) -> usize { self.0.len() }
}
#[inline(always)]
pub(crate) fn clear_private_salt(salt:&mut[u8;32]) {
    // SAFETY: the caller supplies a uniquely borrowed salt cell.
    unsafe {core::ptr::write_volatile(salt,[0;32]);}
}
impl Drop for PrivateSalts {
    fn drop(&mut self) {
        let mut index=0;
        while index<self.0.len() {
            clear_private_salt(&mut self.0[index]);
            index+=1;
        }
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}
impl Commitment {
    pub fn new_salted(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
        salts: PrivateSalts,
    ) -> Result<Self, Error> {
        Self::build(hash, domain, time, messages, variant, Some(salts))
    }
    fn build(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
        private_salts: Option<PrivateSalts>,
    ) -> Result<Self, Error> {
        if messages.len() != LANES {
            return Err(Error::WrongLength);
        }
        if private_salts.as_ref().is_some_and(|salts| salts.len() != FIBRE_COUNT) {
            return Err(Error::WrongLength);
        }
        let lanes=commitment_lanes(time)?;
        let words=encode_commitment_words(domain,messages,variant,&lanes)?;
        let leaves=commitment_leaves(hash,time,&lanes,&words,private_salts.as_ref())?;
        Ok(Self {
            time,
            lanes,
            words,
            tree: crate::host_tree::BinaryTree::new(aspis_core::digest::LegacyHashFn(hash), leaves)
                .ok_or(Error::WrongLength)?,
            private_salts,
        })
    }
    pub fn root(&self) -> [u8; 32] {
        self.tree.root()
    }
    /// Binary multiproof for strictly increasing indices.
    pub(crate) fn multiproof(&self, indices: &[u32]) -> Option<Vec<u8>> {
        self.tree.multiproof(indices)
    }
    pub(crate) fn fill_opening(&self, u: FibreIndex, out: &mut FibreOpening) {
        out.values=fill_opening_values(self,u,out.values,0);
        // No per-query path: authentication is the batch multiproof.
        let path=opening_path(self.time);
        out.paths[path]=[[[0;32];7];6];
    }
    pub(crate) fn opening_salt(&self, u: FibreIndex) -> Option<&[u8; 32]> {
        match &self.private_salts {Some(salts)=>Some(salts.get(u.get())),None=>None}
    }
}


fn commitment_lanes(time:CommitmentTime)->Result<Vec<usize>,Error> {
    match time {
        CommitmentTime::C1=>{
            let mut lanes=filled(27,0)?;
            lanes.copy_from_slice(&[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,28]);
            Ok(lanes)
        }
        CommitmentTime::C2=>{
            let mut lanes=filled(2,0)?;
            lanes.copy_from_slice(&[26,27]);
            Ok(lanes)
        }
    }
}

fn validate_commitment_lanes(messages:&[Message<E>],lanes:&[usize])->Result<(),Error> {
            let mut i=0;
            while i<lanes.len() {
                validate_lane(&messages[lanes[i]],lanes[i])?;
                i+=1;
            }
    Ok(())
}
fn encode_commitment_words(domain:&EncodingDomain,messages:&[Message<E>],variant:crate::transport::Variant,lanes:&[usize])->Result<Vec<Word>,Error> {
    let mut words = Vec::new();
        words
            .try_reserve_exact(lanes.len())
            .map_err(|_| Error::Allocation)?;
        #[cfg(feature="ct-host-prover")]
        {
            // Validate in source order before launching a public lane partition.
            validate_commitment_lanes(messages,lanes)?;
            let encoded=crate::host_work::map(200,lanes.len(),|i| {
                encode_commitment_lane(domain,messages,variant,lanes[i])
            });
            let mut encoded=encoded;
            // Consume in ascending lane order without copying encoded words.
            let mut i=0;
            while i<encoded.len()/2 {
                let j=encoded.len()-1-i;
                encoded.swap(i,j);
                i+=1;
            }
            while !encoded.is_empty() {let word=encoded.pop().unwrap()?;words.push(word);}
        }
        #[cfg(not(feature="ct-host-prover"))]
        {
        for &l in &lanes {
            if messages[l].iter().any(|x| {
                x.to_limbs()[if l < 26 { 1 } else { 4 }..]
                    .iter()
                    .any(|&d| d != 0)
            }) {
                return Err(Error::WrongField);
            }
            // API inputs and retained matching data are semantic rows; only
            // Enc consumes coefficients. W_l = Enc(t_l ∘ π⁻¹), D13.
            let coefficients = variant.coefficients(&messages[l]);
            words.push(if l < 26 {
                Word::Base(domain.encode(&coefficients.map(|x| M31(x.to_limbs()[0])))?)
            } else {
                Word::Secure(domain.encode(&coefficients.map(|x| x.c0()))?)
            });
        }
        }
    Ok(words)
}
fn encode_commitment_lane(domain:&EncodingDomain,messages:&[Message<E>],variant:crate::transport::Variant,lane:usize)->Result<Word,Error> {
    let coefficients=variant.coefficients(&messages[lane]);
    if lane<26 {
        let base=base_coefficients(&coefficients);
        Ok(Word::Base(domain.encode(&base)?))
    } else {
        let secure=secure_coefficients(&coefficients);
        Ok(Word::Secure(domain.encode(&secure)?))
    }
}
fn base_coefficients(coefficients:&Message<E>)->Message<M31> {
    let mut out=[M31::ZERO;1024];let mut i=0;
    while i<1024 {let value=M31(coefficients[i].to_limbs()[0]);out[i]=value;i+=1;}
    out
}
fn secure_coefficients(coefficients:&Message<E>)->Message<QM31> {
    let mut out=[QM31::ZERO;1024];let mut i=0;
    while i<1024 {let value=coefficients[i].c0();out[i]=value;i+=1;}
    out
}

fn commitment_leaves(hash:HashFn,time:CommitmentTime,lanes:&[usize],words:&[Word],private_salts:Option<&PrivateSalts>)->Result<Vec<[u8;32]>,Error> {
    let leaves=filled(FIBRE_COUNT,[0;32])?;
    let tag=commitment_tag(time);
    let leaves=match private_salts {
        Some(salts)=>salted_commitment_leaves(hash,tag,lanes,words,salts,leaves),
        None=>plain_commitment_leaves(hash,tag,lanes,words,leaves),
    };
    Ok(leaves)
}
fn commitment_tag(time:CommitmentTime)->u8 {
    match time {CommitmentTime::C1=>merkle::C1_TAG,CommitmentTime::C2=>merkle::C2_TAG}
}
fn salted_commitment_leaves(hash:HashFn,tag:u8,lanes:&[usize],words:&[Word],salts:&PrivateSalts,mut leaves:Vec<[u8;32]>)->Vec<[u8;32]> {
    let count=leaves.len();let mut u=0;
    while u<count {
        let (bytes,at)=commitment_leaf_bytes(words,lanes,u);
        let salt=salts.get(u);
        let leaf=aspis_core::state_only_private_merkle::private_leaf_hash(hash,tag,&bytes[..at],salt);
        leaves[u]=leaf;u+=1;
    }
    leaves
}
fn plain_commitment_leaves(hash:HashFn,tag:u8,lanes:&[usize],words:&[Word],mut leaves:Vec<[u8;32]>)->Vec<[u8;32]> {
    let count=leaves.len();let mut u=0;
    while u<count {
        let (bytes,at)=commitment_leaf_bytes(words,lanes,u);
        let leaf=merkle::leaf(hash,tag,&bytes[..at]);
        leaves[u]=leaf;u+=1;
    }
    leaves
}

fn commitment_leaf_bytes(words:&[Word],lanes:&[usize],u:usize)->([u8;480],usize) {
            let mut bytes = [0u8; 480];
            let mut at = 0;
            let mut s=0;
            while s<4 {
                let mut j=0;
                while j<lanes.len() {
                    let b=words[j].value(4*u+s).to_le_bytes();
                    let width=if lanes[j]<26 {4} else {16};
                    bytes[at..at+width].copy_from_slice(&b[..width]);at+=width;
                    j+=1;
                }
                s+=1;
            }
    (bytes,at)
}

fn validate_lane(message:&Message<E>,lane:usize)->Result<(),Error> {
    let first=if lane<26 {1} else {4};
    let mut row=0;
    while row<1024 {
        let limbs=message[row].to_limbs();
        validate_zero_tail(&limbs,first)?;row+=1;
    }
    Ok(())
}
fn validate_zero_tail(limbs:&[u32;8],mut i:usize)->Result<(),Error> {
    while i<8 {if limbs[i]!=0 {return Err(Error::WrongField);}i+=1;}
    Ok(())
}

fn opening_lane_values(word:&Word,u:FibreIndex)->[E;4] {
    let at=4*u.get();
    [word.value(at),word.value(at+1),word.value(at+2),word.value(at+3)]
}

fn fill_opening_values(c:&Commitment,u:FibreIndex,mut values:[[E;29];4],j:usize)->[[E;29];4] {
    if j==c.lanes.len() {return values;}
    let lane=c.lanes[j];
    let row=opening_lane_values(&c.words[j],u);
    values[0][lane]=row[0];values[1][lane]=row[1];
    values[2][lane]=row[2];values[3][lane]=row[3];
    fill_opening_values(c,u,values,j+1)
}
fn opening_path(time:CommitmentTime)->usize {match time {CommitmentTime::C1=>0,CommitmentTime::C2=>1}}
