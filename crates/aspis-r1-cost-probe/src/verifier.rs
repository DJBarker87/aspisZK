//! UNPROVED R1 COST PROBE. Two-transaction verifier shape; no production use.
use aspis_core::r0::CodeField;
use alloc::{boxed::Box,vec::Vec};
use aspis_core::{HashFn,field::{WideExact as E,QM31 as K,M31},circle::SecureCirclePoint,r0::{domain,merkle}};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
use crate::{transport::Variant,weights::{self,Weights,field,powers,QUARTER},transcript::Transcript};

pub const SEMANTIC_BYTES:usize=12903+29*32;
pub const HEADER:usize=16;
pub const INITIAL_QUERY_BYTES:usize=480+128+2*6*7*32;
pub const SECOND_QUERY_BYTES:usize=4*32+6*7*32;
pub const CHECKPOINT_FIXED:usize=16+32*3+64+32*5+88+160+64+32*3+32;
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Phase { Parsed,Semantic,Prepare,CheckpointRead,Merkle(usize),Query(usize),CheckpointWrite,Relation,Final }
pub type Observer=Option<fn(Phase)>;
fn mark(obs:Observer,p:Phase) { if let Some(f)=obs {f(p);} }
pub fn checkpoint_size(v:Variant)->usize {CHECKPOINT_FIXED+32*v.final_len()}

pub struct View<'a> {
    pub variant:Variant,pub semantic:&'a[u8],pub y1:&'a[u8],pub inactive:E,
    pub round0:&'a[u8],pub folded_root:Option<&'a[u8;32]>,pub round1:&'a[u8],
    pub final_message:&'a[u8],pub query_bytes:&'a[u8],
}
fn echeck(b:&[u8],k:bool)->Result<(),Error> {
    for c in b.chunks_exact(32) {let x=E::from_le_bytes(c).ok_or(Error::Parse)?;if k&&x.c1()!=K::ZERO {return Err(Error::Parse);}}
    Ok(())
}
impl<'a> View<'a> {
    pub fn proof_bytes(v:Variant)->usize {HEADER+SEMANTIC_BYTES+29*32+32+7*32+if v.folds()==2 {32+7*32}else{0}+v.final_len()*32+22*(INITIAL_QUERY_BYTES+if v.folds()==2 {SECOND_QUERY_BYTES}else{0})}
    #[inline(never)]
    pub fn parse(bytes:&'a[u8])->Result<Self,Error> {
        if bytes.len()<HEADER||&bytes[..8]!=b"R1P2COST"||bytes[9..16].iter().any(|&x|x!=0) {return Err(Error::Parse);}
        let v=Variant::from_tag(bytes[8]).ok_or(Error::Parse)?;
        if bytes.len()!=Self::proof_bytes(v) {return Err(Error::Parse);}
        let mut at=HEADER;
        let semantic=&bytes[at..at+SEMANTIC_BYTES];at+=SEMANTIC_BYTES;
        let y1=&bytes[at..at+29*32];at+=29*32;echeck(y1,true)?;
        let inactive=E::from_le_bytes(&bytes[at..at+32]).ok_or(Error::Parse)?;at+=32;
        let round0=&bytes[at..at+7*32];at+=7*32;echeck(round0,false)?;
        let (folded_root,round1)=if v.folds()==2 {
            let root=bytes[at..at+32].try_into().unwrap();at+=32;
            let round=&bytes[at..at+7*32];at+=7*32;echeck(round,false)?;(Some(root),round)
        }else{(None,&[][..])};
        let final_message=&bytes[at..at+v.final_len()*32];at+=v.final_len()*32;echeck(final_message,false)?;
        let query_bytes=&bytes[at..];
        let out=Self{variant:v,semantic,y1,inactive,round0,folded_root,round1,final_message,query_bytes};
        for i in 0..22 {
            let q=out.query(i);
            for s in 0..4 {
                for l in 0..26 {M31::from_le_bytes(q[s*120+l*4..s*120+l*4+4].try_into().unwrap()).ok_or(Error::Parse)?;}
                K::from_le_bytes(&q[s*120+104..s*120+120]).ok_or(Error::Parse)?;
                for l in 0..2 {K::from_le_bytes(&q[480+s*32+l*16..480+s*32+l*16+16]).ok_or(Error::Parse)?;}
            }
            if v.folds()==2 {echeck(&q[INITIAL_QUERY_BYTES..INITIAL_QUERY_BYTES+128],false)?;}
        }
        Ok(out)
    }
    pub fn query(&self,i:usize)->&'a[u8] {let width=INITIAL_QUERY_BYTES+if self.variant.folds()==2 {SECOND_QUERY_BYTES}else{0};&self.query_bytes[i*width..(i+1)*width]}
}

pub struct Prepared {
    pub variant:Variant,pub roots:[[u8;32];2],pub gamma:E,pub kappa:E,pub alpha:[E;2],pub rho:E,
    pub queries:[u32;22],pub semantic_alpha:[K;10],pub z:[SecureCirclePoint;2],pub claim:E,pub state:[u8;32],
}
impl Prepared {
    #[inline(never)]
    pub fn new(sem:&crate::r1_semantic::Verified,v:&View<'_>,hash:HashFn)->Result<Box<Self>,Error> {
        let mut t=Transcript::new(hash,sem.transcript.state(),v.variant);
        let gamma=t.scalar(27,v.y1,true);
        let kappa=t.scalar(28,&v.inactive.to_le_bytes(),false);
        let mut alpha=[t.scalar(29,v.round0,false),E::ZERO];
        if v.variant.folds()==2 {
            let mut bytes=Vec::with_capacity(32+224);bytes.extend_from_slice(v.folded_root.unwrap());bytes.extend_from_slice(v.round1);
            alpha[1]=t.scalar(30,&bytes,false);
        }
        let row=if v.variant.folds()==1 {30}else{31};
        let queries=t.queries(row,v.final_message)?;
        let rho=t.scalar(row+1,&[],false);
        let g=powers::<29>(gamma);let k=powers::<7>(kappa);
        let mut parts=[E::ZERO;7];parts[0]=v.inactive;
        for l in 0..29 {
            for point in 0..3 {parts[point+1]=parts[point+1].add(g[l].mul_qm31(sem.claims[point][l]));}
            parts[4]=parts[4].add(g[l].mul_qm31(sem.extra[l]));
            parts[5]=parts[5].add(g[l].mul_qm31(sem.before_z1[l]));
            parts[6]=parts[6].add(g[l].mul_qm31(field(v.y1,l).c0()));
        }
        let mut claim=E::ZERO;
        for i in 0..7 {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace::value(14,7,claim);
        Ok(Box::new(Self{variant:v.variant,roots:sem.roots,gamma,kappa,alpha,rho,queries,semantic_alpha:sem.alpha,z:sem.z,claim,state:t.state}))
    }
}
pub struct Accumulator { pub weights:Vec<E>,pub rhs:E,pub power:E,pub next:usize }
impl Accumulator {
    pub fn new(v:Variant)->Result<Self,Error> {Ok(Self{weights:aspis_core::r0::heap::filled(v.final_len(),E::ZERO).map_err(|_|Error::Allocation)?,rhs:E::ZERO,power:E::ONE,next:0})}
}

fn merkle_path(hash:HashFn,root:&[u8;32],mut index:usize,mut node:[u8;32],path:&[u8])->bool {
    for d in 0..6 {
        let slot=index%8;
        let children=core::array::from_fn(|s| {
            if s==slot {node}else{let j=s-usize::from(s>slot);path[d*224+j*32..d*224+j*32+32].try_into().unwrap()}
        });
        node=merkle::parent(hash,&children);index/=8;
    }
    node==*root&&index==0
}
pub fn four_dots(q:&[u8],g:&[E;29])->[E;4] {
    core::array::from_fn(|s| {
        let mut a=E::ZERO;
        for l in 0..26 {a=a.add(g[l].mul_m31(M31::from_le_bytes(q[s*120+l*4..s*120+l*4+4].try_into().unwrap()).unwrap()));}
        a=a.add(g[28].mul_qm31(K::from_le_bytes(&q[s*120+104..s*120+120]).unwrap()));
        for l in 0..2 {a=a.add(g[l+26].mul_qm31(K::from_le_bytes(&q[480+s*32+l*16..480+s*32+l*16+16]).unwrap()));}
        a
    })
}
pub fn circle_fold(alpha:E,u:usize,a:[E;4])->E {
    let p=domain::fibre_point::<M31>(domain::FibreIndex::new(u).unwrap());
    let ix=p.x.inv();let iy=p.y.inv();let [a,b,c,d]=a;
    let h0=a.add(b).add(c).add(d).mul_m31(QUARTER);
    let h1=a.sub(b).sub(c).add(d).mul_m31(QUARTER.mul(iy));
    let h2=a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(ix));
    let h3=a.sub(b).add(c).sub(d).mul_m31(QUARTER.mul(ix).mul(iy));
    h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
}
pub fn line_fold(alpha:E,v:usize,a:[E;4])->E {
    let x=domain::line_node::<M31>(domain::FibreIndex::new(4*v).unwrap());
    let y=domain::line_node::<M31>(domain::FibreIndex::new(4*v+3).unwrap());
    let z=x.mul(x).double().sub(M31::ONE);
    let half=M31(1073741824);
    let [a,b,c,d]=a;
    let h0=a.add(b).add(c).add(d).mul_m31(QUARTER);
    let h2=a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(z.inv()));
    let c0=a.sub(b).mul_m31(half.mul(x.inv()));
    let c1=d.sub(c).mul_m31(half.mul(y.inv()));
    let h1=c0.add(c1).mul_m31(half);
    let h3=c0.sub(c1).mul_m31(half.mul(z.inv()));
    h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
}
#[inline(never)]
pub fn accumulate(p:&Prepared,a:&mut Accumulator,index:usize,value:E) {
    let mut node=domain::line_node::<M31>(domain::FibreIndex::new(if p.variant.folds()==1 {index}else{index/4*4}).unwrap());
    if p.variant.folds()==2 {for _ in 0..2 {node=node.mul(node).double().sub(M31::ONE);}}
    let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let mut n=1;
    while n<a.weights.len() {for j in 0..n {basis[n+j]=basis[j].mul(node);} node=node.mul(node).double().sub(M31::ONE);n*=2;}
    for j in 0..a.weights.len() {
        a.weights[j]=a.weights[j].add(a.power.mul_m31(basis[j]));
        crate::trace::value(12,a.next*a.weights.len()+j,a.weights[j]);
        crate::trace::value(13,a.next*a.weights.len()+j,E::from_m31(basis[j]));
    }
    a.rhs=a.rhs.add(a.power.mul(value));crate::trace::value(11,a.next,a.rhs);
    a.power=a.power.mul(p.rho);a.next+=1;
}
#[inline(never)]
pub fn query(v:&View<'_>,p:&Prepared,a:&mut Accumulator,g:&[E;29],hash:HashFn,obs:Observer)->Result<(),Error> {
    let i=a.next;let u=p.queries[i] as usize;let q=v.query(i);
    let c1=merkle::leaf(hash,merkle::C1_TAG,&q[..480]);let c2=merkle::leaf(hash,merkle::C2_TAG,&q[480..608]);
    if !merkle_path(hash,&p.roots[0],u,c1,&q[608..608+1344])||!merkle_path(hash,&p.roots[1],u,c2,&q[608+1344..INITIAL_QUERY_BYTES]) {return Err(Error::Merkle);}
    if p.variant.folds()==2 {
        let folded=&q[INITIAL_QUERY_BYTES..INITIAL_QUERY_BYTES+128];
        if !merkle_path(hash,v.folded_root.unwrap(),u/4,merkle::leaf(hash,0x72,folded),&q[INITIAL_QUERY_BYTES+128..]) {return Err(Error::Merkle);}
    }
    mark(obs,Phase::Merkle(i));
    let dots=four_dots(q,g);for s in 0..4 {crate::trace::value(9,4*i+s,dots[s]);}
    let mut folded=circle_fold(p.alpha[0],u,dots);crate::trace::value(10,2*i,folded);
    if p.variant.folds()==2 {
        let values=core::array::from_fn(|s|field(&q[INITIAL_QUERY_BYTES..],s));
        if folded!=values[u%4] {return Err(Error::Query);}
        folded=line_fold(p.alpha[1],u/4,values);crate::trace::value(10,2*i+1,folded);
    }
    accumulate(p,a,u,folded);mark(obs,Phase::Query(i));Ok(())
}
pub fn polynomial(bytes:&[u8],x:E)->E {(0..7).rev().fold(E::ZERO,|a,i|a.mul(x).add(field(bytes,i)))}
#[inline(never)]
pub fn finish_relation(v:&View<'_>,p:&Prepared,a:&Accumulator,obs:Observer)->Result<(),Error> {
    let mut claim=p.claim;
    for round in 0..p.variant.folds() {
        let poly=if round==0 {v.round0}else{v.round1};
        let lhs=field(poly,0).add(field(poly,4));let rhs=claim.mul_m31(QUARTER);
        crate::trace::value(15,3*round,lhs);crate::trace::value(15,3*round+1,rhs);
        if lhs!=rhs {return Err(Error::Relation);}
        claim=polynomial(poly,p.alpha[round]);crate::trace::value(15,3*round+2,claim);
    }
    let weights=Weights::new(p.variant,&p.semantic_alpha,&p.z)?;
    let pair=weights.pair(&p.alpha[..p.variant.folds()],v.final_message,p.kappa)?;
    crate::trace::value(16,0,pair);crate::trace::value(16,1,claim);
    if pair!=claim {return Err(Error::Relation);}
    mark(obs,Phase::Relation);
    let actual=a.weights.iter().enumerate().fold(E::ZERO,|s,(j,w)|s.add(field(v.final_message,j).mul(*w)));
    crate::trace::value(17,0,actual);crate::trace::value(17,1,a.rhs);
    if a.next!=22||actual!=a.rhs {return Err(Error::Query);}
    mark(obs,Phase::Final);Ok(())
}

fn put(out:&mut Vec<u8>,x:E) {out.extend_from_slice(&x.to_le_bytes());}
pub fn checkpoint(p:&Prepared,a:&Accumulator,proof:&[u8],public:&[u8],hash:HashFn)->Vec<u8> {
    let mut out=Vec::with_capacity(checkpoint_size(p.variant));
    out.extend_from_slice(b"R1P2CKPT");out.extend_from_slice(&[p.variant.tag(),a.next as u8,1,0,0,0,0,0]);
    out.extend_from_slice(&hash(&[proof]));out.extend_from_slice(&hash(&[public]));out.extend_from_slice(&p.state);
    for root in &p.roots {out.extend_from_slice(root);}
    for x in [p.gamma,p.kappa,p.alpha[0],p.alpha[1],p.rho] {put(&mut out,x);}
    for q in p.queries {out.extend_from_slice(&q.to_le_bytes());}
    for x in p.semantic_alpha {let mut b=[0;16];x.write_le_bytes(&mut b);out.extend_from_slice(&b);}
    for z in p.z {for x in [z.x,z.y] {let mut b=[0;16];x.write_le_bytes(&mut b);out.extend_from_slice(&b);}}
    for x in [p.claim,a.rhs,a.power] {put(&mut out,x);}
    for &x in &a.weights {put(&mut out,x);}
    let sum=hash(&[b"UNPROVED:R1:checkpoint",&out]);out.extend_from_slice(&sum);
    assert_eq!(out.len(),checkpoint_size(p.variant));out
}
struct Reader<'a>{bytes:&'a[u8],at:usize}
impl<'a> Reader<'a>{
    fn raw<const N:usize>(&mut self)->[u8;N] {let b=self.bytes[self.at..self.at+N].try_into().unwrap();self.at+=N;b}
    fn e(&mut self)->Result<E,Error>{E::from_le_bytes(&self.raw::<32>()).ok_or(Error::Checkpoint)}
    fn k(&mut self)->Result<K,Error>{K::from_le_bytes(&self.raw::<16>()).ok_or(Error::Checkpoint)}
}
#[inline(never)]
pub fn resume(bytes:&[u8],proof:&[u8],public:&[u8],v:Variant,hash:HashFn)->Result<(Box<Prepared>,Accumulator),Error> {
    if bytes.len()!=checkpoint_size(v)||&bytes[..8]!=b"R1P2CKPT"||bytes[8]!=v.tag()||bytes[9]>22||bytes[10]!=1||bytes[11..16].iter().any(|&b|b!=0) {return Err(Error::Checkpoint);}
    let end=bytes.len()-32;
    if bytes[16..48]!=hash(&[proof])||bytes[48..80]!=hash(&[public])||bytes[end..]!=hash(&[b"UNPROVED:R1:checkpoint",&bytes[..end]]) {return Err(Error::Checkpoint);}
    let mut r=Reader{bytes,at:80};let state=r.raw();let roots=[r.raw(),r.raw()];
    let gamma=r.e()?;let kappa=r.e()?;let alpha=[r.e()?,r.e()?];let rho=r.e()?;
    let queries=core::array::from_fn(|_|u32::from_le_bytes(r.raw()));
    for (i,q) in queries.iter().enumerate(){if *q>=1<<18||queries[..i].contains(q){return Err(Error::Checkpoint);}}
    let mut semantic_alpha=[K::ZERO;10];for x in &mut semantic_alpha {*x=r.k()?;}
    let z=[SecureCirclePoint{x:r.k()?,y:r.k()?},SecureCirclePoint{x:r.k()?,y:r.k()?}];
    let claim=r.e()?;let rhs=r.e()?;let power=r.e()?;
    let mut weights=aspis_core::r0::heap::filled(v.final_len(),E::ZERO).map_err(|_|Error::Allocation)?;
    for x in &mut weights {*x=r.e()?;}
    if r.at!=end {return Err(Error::Checkpoint);}
    Ok((Box::new(Prepared{variant:v,roots,gamma,kappa,alpha,rho,queries,semantic_alpha,z,claim,state}),Accumulator{weights,rhs,power,next:bytes[9] as usize}))
}
#[inline(never)]
pub fn tx1(public:Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize,hash:HashFn,obs:Observer)->Result<Vec<u8>,Error> {
    if k>22 {return Err(Error::Parse);}
    let v=View::parse(proof)?;mark(obs,Phase::Parsed);
    let sem=crate::r1_semantic::verify(public,v.semantic,hash).map_err(|_|Error::Semantic)?;mark(obs,Phase::Semantic);
    let p=Prepared::new(&sem,&v,hash)?;let mut a=Accumulator::new(v.variant)?;let g=powers::<29>(p.gamma);mark(obs,Phase::Prepare);
    while a.next<k {query(&v,&p,&mut a,&g,hash,obs)?;}
    let bytes=checkpoint(&p,&a,proof,public_bytes,hash);mark(obs,Phase::CheckpointWrite);Ok(bytes)
}
#[inline(never)]
pub fn tx2(public_bytes:&[u8],proof:&[u8],checkpoint:&[u8],hash:HashFn,obs:Observer)->Result<(),Error> {
    let v=View::parse(proof)?;mark(obs,Phase::Parsed);
    let (p,mut a)=resume(checkpoint,proof,public_bytes,v.variant,hash)?;let g=powers::<29>(p.gamma);mark(obs,Phase::CheckpointRead);
    while a.next<22 {query(&v,&p,&mut a,&g,hash,obs)?;}
    finish_relation(&v,&p,&a,obs)
}
