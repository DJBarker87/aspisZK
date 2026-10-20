#![allow(dead_code)]
const P:u32=0x7fffffff;
#[derive(Clone,Copy,Debug,kani::Arbitrary)] struct M31(u32);
#[derive(Clone,Copy,Debug,kani::Arbitrary)] struct CM31 {a:M31,b:M31}
#[derive(Clone,Copy,Debug,kani::Arbitrary)] struct QM31 {c0:CM31,c1:CM31}
type K=QM31;
#[derive(Clone,Copy,Debug,kani::Arbitrary)] enum Error {Checkpoint}
fn cm_ok(x:CM31)->bool {x.a.0<P && x.b.0<P}
fn k_ok(x:K)->bool {cm_ok(x.c0)&&cm_ok(x.c1)}
impl M31 {
#[kani::ensures(|r:&Option<M31>| r.as_ref().map_or(true, |x| x.0<P))]
pub fn from_le_bytes(bytes: [u8; 4]) -> Option<M31> {
        let v = u32::from_le_bytes(bytes);
        if v >= P {
            None
        } else {
            Some(M31(v))
        }
    }
}
#[kani::proof_for_contract(M31::from_le_bytes)]
fn decoder_m31() {let b:[u8;4]=kani::any(); M31::from_le_bytes(b);}
impl CM31 {
#[kani::requires(bytes.len()==8)]
#[kani::ensures(|r:&Option<CM31>| r.as_ref().map_or(true, |x| cm_ok(*x)))]
pub fn from_le_bytes(bytes: &[u8]) -> Option<CM31> {
        let a_bytes = match bytes[0..4].try_into() {
            Ok(value) => value,
            Err(_) => return None,
        };
        let a = M31::from_le_bytes(a_bytes)?;
        let b_bytes = match bytes[4..8].try_into() {
            Ok(value) => value,
            Err(_) => return None,
        };
        let b = M31::from_le_bytes(b_bytes)?;
        Some(CM31 { a, b })
    }
}
#[kani::proof_for_contract(CM31::from_le_bytes)]
#[kani::stub_verified(M31::from_le_bytes)]
fn decoder_cm31() {let b:[u8;8]=kani::any(); CM31::from_le_bytes(&b);}
impl QM31 {
#[kani::requires(bytes.len()==16)]
#[kani::ensures(|r:&Option<QM31>| r.as_ref().map_or(true, |x| k_ok(*x)))]
pub fn from_le_bytes(bytes: &[u8]) -> Option<QM31> {
        let c0 = CM31::from_le_bytes(&bytes[0..8])?;
        let c1 = CM31::from_le_bytes(&bytes[8..16])?;
        Some(QM31 { c0, c1 })
    }
}
#[kani::proof_for_contract(QM31::from_le_bytes)]
#[kani::stub_verified(CM31::from_le_bytes)]
fn decoder_qm31() {let b:[u8;16]=kani::any(); QM31::from_le_bytes(&b);}
struct Reader<'a>{bytes:&'a[u8],at:usize}
impl Reader<'_> {
#[kani::requires(N<=32 && self.bytes.len()<=4880 && N<=self.bytes.len() && self.at<=self.bytes.len()-N)]
#[kani::modifies(&mut self.at)]
#[kani::ensures(|_r:&[u8;N]| self.at==old(self.at)+N && self.at<=self.bytes.len())]
fn raw<const N:usize>(&mut self)->[u8;N] {let b=self.bytes[self.at..self.at+N].try_into().unwrap();self.at+=N;b}
#[kani::requires(self.bytes.len()<=4880 && self.bytes.len()>=16 && self.at<=self.bytes.len()-16)]
#[kani::modifies(&mut self.at)]
#[kani::ensures(|r:&Result<K,Error>| self.at==old(self.at)+16 && r.as_ref().map_or(true, |x| k_ok(*x)))]
fn k(&mut self)->Result<K,Error>{K::from_le_bytes(&self.raw::<16>()).ok_or(Error::Checkpoint)}
}
#[kani::proof_for_contract(Reader::raw::<4>)] #[kani::unwind(34)]
fn reader_raw4() {let b:[u8;4880]=kani::any();let len:usize=kani::any();kani::assume(len<=4880); let mut r=Reader{bytes:&b[..len],at:kani::any()}; r.raw::<4>();}
#[kani::proof_for_contract(Reader::raw::<16>)] #[kani::unwind(34)]
fn reader_raw16() {let b:[u8;4880]=kani::any();let len:usize=kani::any();kani::assume(len<=4880); let mut r=Reader{bytes:&b[..len],at:kani::any()}; r.raw::<16>();}
#[kani::proof_for_contract(Reader::raw::<32>)] #[kani::unwind(34)]
fn reader_raw32() {let b:[u8;4880]=kani::any();let len:usize=kani::any();kani::assume(len<=4880); let mut r=Reader{bytes:&b[..len],at:kani::any()}; r.raw::<32>();}
#[kani::proof_for_contract(Reader::k)]
#[kani::stub_verified(Reader::raw::<16>)] #[kani::stub_verified(QM31::from_le_bytes)]
fn reader_k() {let b:[u8;4880]=kani::any();let len:usize=kani::any();kani::assume(len<=4880);let mut r=Reader{bytes:&b[..len],at:kani::any()};r.k();}
#[kani::requires(bytes.len()<=4880 && bytes.len()>=160 && at<=bytes.len()-160)]
#[kani::ensures(|r:&Result<([K;10],usize),Error>| r.as_ref().map_or(true, |(ks,end)| *end==at+160 && k_ok(ks[0]) && k_ok(ks[1]) && k_ok(ks[2]) && k_ok(ks[3]) && k_ok(ks[4]) && k_ok(ks[5]) && k_ok(ks[6]) && k_ok(ks[7]) && k_ok(ks[8]) && k_ok(ks[9])))]
fn read_checkpoint_semantic_alpha(bytes:&[u8],at:usize)->Result<([K;10],usize),Error> {
    let mut r=Reader{bytes,at};
    let values=[
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
        r.k()?,
    ];
    Ok((values,r.at))
}
#[kani::proof_for_contract(read_checkpoint_semantic_alpha)] #[kani::unwind(12)]
#[kani::stub_verified(Reader::k)]
fn semantic_alpha() {let b:[u8;4880]=kani::any();let len:usize=kani::any();kani::assume(len<=4880);read_checkpoint_semantic_alpha(&b[..len],kani::any());}
#[kani::requires(bytes.len()<=4880 && weights.len()<=256 && 16*weights.len()<=bytes.len() && at<=bytes.len()-16*weights.len())]
#[kani::ensures(|r:&Result<(Vec<K>,usize),Error>| r.as_ref().map_or(true, |(ks,end)| ks.len()==old(weights.len()) && *end==at+16*ks.len() && ks.iter().all(|x| k_ok(*x))))]
fn read_checkpoint_weights(bytes:&[u8],mut at:usize,mut weights:Vec<K>)->Result<(Vec<K>,usize),Error> {
    for out in &mut weights {
        read_one_weight(bytes,&mut at,out)?;
    }
    Ok((weights,at))
}
#[kani::proof_for_contract(read_checkpoint_weights)] #[kani::unwind(258)]
#[kani::stub_verified(read_one_weight)]
fn checkpoint_weights256() {let b:[u8;4880]=kani::any(); let w=kani::vec::any_vec::<K,256>(); let len:usize=kani::any();kani::assume(len<=4880);read_checkpoint_weights(&b[..len],kani::any(),w);}
#[kani::requires(bytes.len()<=4880 && bytes.len()>=16 && *at<=bytes.len()-16)]
#[kani::modifies(at,out)]
#[kani::ensures(|r:&Result<(),Error>| r.is_err() || (*at==old(*at)+16 && k_ok(*out)))]
fn read_one_weight(bytes:&[u8],at:&mut usize,out:&mut K)->Result<(),Error> {
    let mut reader=Reader{bytes,at:*at};
    let value=reader.k()?;
    *at=reader.at;
    *out=value;
    Ok(())
}
#[kani::proof_for_contract(read_one_weight)]
#[kani::stub_verified(Reader::k)]
fn weight_body() {let b:[u8;4880]=kani::any();let len:usize=kani::any();kani::assume(len<=4880);let mut at=kani::any();let mut out=kani::any();read_one_weight(&b[..len],&mut at,&mut out);}

fn residue_limb_at(row:&[u64;4],index:usize)->u64 {row[index]}

fn power_limb_at(limbs:&[u32;4],index:usize)->u32 {limbs[index]}
const B:u64=1<<34;
const C:u64=(P as u64-1)*(P as u64-1);
fn row_bound(row:&[u64;4],limit:u64)->bool {row[0]<limit && row[1]<limit && row[2]<limit && row[3]<limit}
fn growth(row:&[u64;4],before:[u64;4])->bool {(0..4).all(|i|row[i]<=before[i]+C)}
#[kani::requires(k_ok(power) && basis.0<P && phase<4 && flush==(phase==3) && row_bound(row,B+phase*C))]
#[kani::modifies(row)]
#[kani::ensures(|_:&()| row_bound(row,B+((phase+1)%4)*C))]
fn update_residue_row(row:&mut [u64;4],power:K,basis:M31,flush:bool,phase:u64) {
    let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
    for j in 0..4 {
        let old=residue_limb_at(row,j);
        let limb=power_limb_at(&limbs,j);
        row[j]=old+u64::from(limb)*u64::from(basis.0);
    }
    if flush {
        for limb in &mut *row {*limb=(*limb&0x7fff_ffff)+(*limb>>31);}
    }
}
#[kani::proof_for_contract(update_residue_row)] #[kani::unwind(6)]
fn residue_row() {let mut row=kani::any();update_residue_row(&mut row,kani::any(),kani::any(),kani::any(),kani::any());}
struct BatchedWeights { raw:Vec<[u64;4]>, terms:usize }
impl BatchedWeights {
#[kani::requires((self.raw.len()==64 || self.raw.len()==256) && index<self.raw.len() && self.terms<=22 && k_ok(power) && basis.0<P && row_bound(&self.raw[index],B+(self.terms%4) as u64*C))]
#[kani::modifies(&mut self.raw[index])]
#[kani::ensures(|_:&()| row_bound(&self.raw[index],B+((self.terms+1)%4) as u64*C))]
fn push(&mut self,index:usize,power:K,basis:M31) {
        let flush=self.terms&3==3;
        update_residue_row(&mut self.raw[index],power,basis,flush,(self.terms%4) as u64);
    }
}
#[kani::proof_for_contract(BatchedWeights::push)] #[kani::unwind(258)]
#[kani::stub_verified(update_residue_row)]
fn batched_push64() {let mut w=BatchedWeights{raw:kani::vec::exact_vec::<[u64;4],64>(),terms:kani::any()}; w.push(kani::any(),kani::any(),kani::any());}
#[kani::proof_for_contract(BatchedWeights::push)] #[kani::unwind(258)]
#[kani::stub_verified(update_residue_row)]
fn batched_push256() {let mut w=BatchedWeights{raw:kani::vec::exact_vec::<[u64;4],256>(),terms:kani::any()}; w.push(kani::any(),kani::any(),kani::any());}
mod geometry;
