//! UNPROVED R1 COST PROBE. Two-transaction verifier shape; no production use.
use aspis_core::r0::CodeField;
use alloc::{boxed::Box,vec::Vec};
use aspis_core::{Digest32,field::{WideExact as E,QM31 as K,M31},circle::SecureCirclePoint,r0::{domain,merkle}};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
use crate::{transport::Variant,weights::{self,Weights,field,powers,QUARTER},transcript::Transcript};

pub const SEMANTIC_BYTES:usize=12903+29*32;
pub const HEADER:usize=16;
#[cfg(not(feature = "private-leaf-salts"))]
pub const INITIAL_QUERY_BYTES:usize=480+128+2*6*7*32;
#[cfg(feature = "private-leaf-salts")]
pub const INITIAL_QUERY_BYTES:usize=480+128+64+2*6*7*32;
#[cfg(not(feature = "private-leaf-salts"))]
pub const SECOND_QUERY_BYTES:usize=4*32+6*7*32;
#[cfg(feature = "private-leaf-salts")]
pub const SECOND_QUERY_BYTES:usize=4*32+32+6*7*32;
pub const CHECKPOINT_FIXED:usize=16+32*3+64+32*4+16+88+160+64+32*2+16+32;
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Phase { Parsed,Semantic,SemanticPart(u8),Prepare,CheckpointRead,Merkle(usize),Query(usize),QueryPart(usize,u8),CheckpointWrite,Relation,Final }
pub type Observer=Option<fn(Phase)>;
fn mark(obs:Observer,p:Phase) { if let Some(f)=obs {f(p);} }
pub fn checkpoint_size(v:Variant)->usize {CHECKPOINT_FIXED+16*v.final_len()}

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
    fn parse_shape(bytes:&'a[u8])->Result<Self,Error> {
        #[cfg(not(feature = "private-leaf-salts"))]
        let magic = b"R1P2COST";
        #[cfg(feature = "private-leaf-salts")]
        let magic = b"R1P3COST";
        if bytes.len()<HEADER||&bytes[..8]!=magic||bytes[9..16].iter().any(|&x|x!=0) {return Err(Error::Parse);}
        let v=Variant::from_tag(bytes[8]).ok_or(Error::Parse)?;
        if bytes.len()!=Self::proof_bytes(v) {return Err(Error::Parse);}
        let mut at=HEADER;
        let semantic=&bytes[at..at+SEMANTIC_BYTES];at+=SEMANTIC_BYTES;
        let y1=&bytes[at..at+29*32];at+=29*32;
        let inactive=E::from_le_bytes(&bytes[at..at+32]).ok_or(Error::Parse)?;at+=32;
        let round0=&bytes[at..at+7*32];at+=7*32;
        let (folded_root,round1)=if v.folds()==2 {
            let root=bytes[at..at+32].try_into().unwrap();at+=32;
            let round=&bytes[at..at+7*32];at+=7*32;(Some(root),round)
        }else{(None,&[][..])};
        let final_message=&bytes[at..at+v.final_len()*32];at+=v.final_len()*32;
        let query_bytes=&bytes[at..];
        Ok(Self{variant:v,semantic,y1,inactive,round0,folded_root,round1,final_message,query_bytes})
    }
    #[inline(never)]
    pub fn parse(bytes:&'a[u8])->Result<Self,Error> {
        let out=Self::parse_shape(bytes)?;
        echeck(out.y1,true)?;
        echeck(out.round0,false)?;
        if let Some(round1)=out.folded_root.map(|_|out.round1) {echeck(round1,false)?;}
        echeck(out.final_message,false)?;
        for i in 0..22 {
            let q=out.query(i);
            for s in 0..4 {
                for l in 0..26 {M31::from_le_bytes(q[s*120+l*4..s*120+l*4+4].try_into().unwrap()).ok_or(Error::Parse)?;}
                K::from_le_bytes(&q[s*120+104..s*120+120]).ok_or(Error::Parse)?;
                for l in 0..2 {K::from_le_bytes(&q[480+s*32+l*16..480+s*32+l*16+16]).ok_or(Error::Parse)?;}
            }
            if out.variant.folds()==2 {echeck(&q[INITIAL_QUERY_BYTES..INITIAL_QUERY_BYTES+128],false)?;}
        }
        Ok(out)
    }
    pub fn query(&self,i:usize)->&'a[u8] {let width=INITIAL_QUERY_BYTES+if self.variant.folds()==2 {SECOND_QUERY_BYTES}else{0};&self.query_bytes[i*width..(i+1)*width]}
}

pub struct Prepared {
    pub variant:Variant,pub roots:[[u8;32];2],pub gamma:E,pub kappa:E,pub alpha:[E;2],pub rho:K,
    pub queries:[u32;22],pub semantic_alpha:[K;10],pub z:[SecureCirclePoint;2],pub claim:E,pub state:[u8;32],
}
fn prepared_claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> {
        let k=powers::<7>(kappa);
        let mut parts=[E::ZERO;7];parts[0]=inactive;
        for point in 0..6 {
            let mut dot=crate::fast_pairing::EbyKDot::new();
            for l in 0..29 {
                let scalar=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()};
                dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
            }
            parts[point+1]=dot.finish();
        }
        let mut claim=E::ZERO;
        for i in 0..7 {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace::value(14,7,claim);
        Ok(claim)
}

impl Prepared {
    #[inline(never)]
    pub fn new<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&View<'_>,hash:H,g:&mut [E;29])->Result<Box<Self>,Error> {
        let mut t=Transcript::new(hash,sem.transcript.state(),v.variant);
        let gamma=t.scalar(27,v.y1,true);
        let kappa=t.scalar(28,&v.inactive.to_le_bytes(),false);
        let alpha0=t.scalar(29,v.round0,false);
        let (alpha,row)=if v.variant.folds()==2 {
            let mut bytes=Vec::with_capacity(32+224);bytes.extend_from_slice(v.folded_root.unwrap());bytes.extend_from_slice(v.round1);
            ([alpha0,t.scalar(30,&bytes,false)],31)
        } else {
            ([alpha0,E::ZERO],30)
        };
        let queries=t.queries(row,v.final_message)?;
        let rho=t.scalar_k(row+1,&[]);
        // Reuse this caller-owned scratch array in tx1; it is never serialized.
        *g=powers::<29>(gamma);
        let claim=prepared_claim(sem,v.y1,v.inactive,g,kappa)?;
        Ok(Box::new(Self{variant:v.variant,roots:sem.roots,gamma,kappa,alpha,rho,queries,semantic_alpha:sem.alpha,z:sem.z,claim,state:t.state}))
    }
}
pub struct Accumulator { pub weights:Vec<K>,pub rhs:E,pub power:K,pub next:usize }
impl Accumulator {
    pub fn new(v:Variant)->Result<Self,Error> {Ok(Self{weights:aspis_core::r0::heap::filled(v.final_len(),K::ZERO).map_err(|_|Error::Allocation)?,rhs:E::ZERO,power:K::ONE,next:0})}
}

fn merkle_path<H:Digest32>(hash:H,root:&[u8;32],mut index:usize,mut node:[u8;32],path:&[u8])->bool {
    for d in 0..6 {
        let slot=index%8;
        let children=core::array::from_fn(|s| {
            if s==slot {node}else{let j=s-usize::from(s>slot);path[d*224+j*32..d*224+j*32+32].try_into().unwrap()}
        });
        node=merkle::parent_with_digest(hash,&children);index/=8;
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
    let p=crate::fast_domain::fibre_point(domain::FibreIndex::new(u).unwrap());
    let ix=p.x.inv();let iy=p.y.inv();let [a,b,c,d]=a;
    let h0=a.add(b).add(c).add(d).mul_m31(QUARTER);
    let h1=a.sub(b).sub(c).add(d).mul_m31(QUARTER.mul(iy));
    let h2=a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(ix));
    let h3=a.sub(b).add(c).sub(d).mul_m31(QUARTER.mul(ix).mul(iy));
    h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
}
pub fn line_fold(alpha:E,v:usize,a:[E;4])->E {
    let x=crate::fast_domain::line_node(domain::FibreIndex::new(4*v).unwrap());
    let y=crate::fast_domain::line_node(domain::FibreIndex::new(4*v+3).unwrap());
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
/// The five base-field denominators used to fold one sampled query: circle
/// x/y, followed by line x/y/z. Their inverses are batch-computed once per
/// transaction so each query avoids five independent field inversions.
struct QueryGeometry { start:usize, inverses:Vec<[M31;5]> }
impl QueryGeometry {
    fn for_range(queries:&[u32;22],start:usize,end:usize)->Result<Self,Error> {
        if start>end||end>queries.len(){return Err(Error::Query);}
        let mut denominators=Vec::with_capacity(end-start);
        let mut flat=Vec::with_capacity((end-start)*5);
        for &query in &queries[start..end] {
            let u=query as usize;
            let fibre=domain::FibreIndex::new(u).map_err(|_|Error::Query)?;
            let point=crate::fast_domain::fibre_point(fibre);
            let line_x=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4).map_err(|_|Error::Query)?);
            let line_y=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4+3).map_err(|_|Error::Query)?);
            let line_z=line_x.mul(line_x).double().sub(M31::ONE);
            let values=[point.x,point.y,line_x,line_y,line_z];
            if values.iter().any(|x|*x==M31::ZERO){return Err(Error::Query);}
            flat.extend_from_slice(&values);
            denominators.push(values);
        }
        if flat.is_empty(){return Ok(Self{start,inverses:Vec::new()});}
        // Standard prefix-product/backward batch inversion. The only `inv`
        // in this routine is applied to the product of all nonzero entries.
        let mut prefixes=Vec::with_capacity(flat.len());
        let mut product=M31::ONE;
        for &value in &flat {prefixes.push(product);product=product.mul(value);}
        let mut suffix_inverse=product.inv();
        let mut flat_inverse=Vec::with_capacity(flat.len());
        flat_inverse.resize(flat.len(),M31::ZERO);
        for i in (0..flat.len()).rev() {
            flat_inverse[i]=suffix_inverse.mul(prefixes[i]);
            suffix_inverse=suffix_inverse.mul(flat[i]);
        }
        let inverses=(0..denominators.len()).map(|i|core::array::from_fn(|j|flat_inverse[5*i+j])).collect();
        Ok(Self{start,inverses})
    }
    #[inline(always)]
    fn for_query(&self,index:usize)->&[M31;5] {&self.inverses[index-self.start]}
}
#[inline(always)]
fn circle_fold_with_inverses(alpha:E,a:[E;4],inverse:&[M31;5])->E {
    let [ix,iy,_,_,_]=*inverse;let [a,b,c,d]=a;
    let h0=a.add(b).add(c).add(d).mul_m31(QUARTER);
    let h1=a.sub(b).sub(c).add(d).mul_m31(QUARTER.mul(iy));
    let h2=a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(ix));
    let h3=a.sub(b).add(c).sub(d).mul_m31(QUARTER.mul(ix).mul(iy));
    h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
}
#[inline(always)]
fn line_fold_with_inverses(alpha:E,a:[E;4],inverse:&[M31;5])->E {
    let [_,_,ix,iy,iz]=*inverse;let half=M31(1073741824);let [a,b,c,d]=a;
    let h0=a.add(b).add(c).add(d).mul_m31(QUARTER);
    let h2=a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(iz));
    let c0=a.sub(b).mul_m31(half.mul(ix));
    let c1=d.sub(c).mul_m31(half.mul(iy));
    let h1=c0.add(c1).mul_m31(half);
    let h3=c0.sub(c1).mul_m31(half.mul(iz));
    h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
}
#[inline(never)]
pub fn accumulate(p:&Prepared,a:&mut Accumulator,index:usize,value:E) {
    let mut node=crate::fast_domain::line_node(domain::FibreIndex::new(if p.variant.folds()==1 {index}else{index/4*4}).unwrap());
    if p.variant.folds()==2 {for _ in 0..2 {node=node.mul(node).double().sub(M31::ONE);}}
    let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let mut n=1;
    while n<a.weights.len() {for j in 0..n {basis[n+j]=basis[j].mul(node);} node=node.mul(node).double().sub(M31::ONE);n*=2;}
    for j in 0..a.weights.len() {
        a.weights[j]=a.weights[j].add(a.power.mul_m31(basis[j]));
        crate::trace::value(12,a.next*a.weights.len()+j,E::from_qm31(a.weights[j]));
        crate::trace::value(13,a.next*a.weights.len()+j,E::from_m31(basis[j]));
    }
    a.rhs=a.rhs.add(value.mul_qm31(a.power));crate::trace::value(11,a.next,a.rhs);
    a.power=a.power.mul(p.rho);a.next+=1;
}
#[inline(never)]
pub fn query<H:Digest32>(v:&View<'_>,p:&Prepared,a:&mut Accumulator,g:&[E;29],hash:H,obs:Observer)->Result<(),Error> {
    let geometry=QueryGeometry::for_range(&p.queries,a.next,a.next+1)?;
    query_with_geometry(v,p,a,g,hash,obs,&geometry)
}
#[inline(never)]
fn query_with_geometry<H:Digest32>(v:&View<'_>,p:&Prepared,a:&mut Accumulator,g:&[E;29],hash:H,obs:Observer,geometry:&QueryGeometry)->Result<(),Error> {
    let i=a.next;let u=p.queries[i] as usize;let q=v.query(i);
    #[cfg(not(feature = "private-leaf-salts"))]
    let (c1,c2,path_at) = (merkle::leaf_with_digest(hash,merkle::C1_TAG,&q[..480]),merkle::leaf_with_digest(hash,merkle::C2_TAG,&q[480..608]),608);
    #[cfg(feature = "private-leaf-salts")]
    let (c1,c2,path_at) = (
        aspis_core::state_only_private_merkle::private_leaf_hash_with_digest(hash,merkle::C1_TAG,&q[..480],q[608..640].try_into().unwrap()),
        aspis_core::state_only_private_merkle::private_leaf_hash_with_digest(hash,merkle::C2_TAG,&q[480..608],q[640..672].try_into().unwrap()),
        672,
    );
    if !merkle_path(hash,&p.roots[0],u,c1,&q[path_at..path_at+1344])||!merkle_path(hash,&p.roots[1],u,c2,&q[path_at+1344..INITIAL_QUERY_BYTES]) {return Err(Error::Merkle);}
    if p.variant.folds()==2 {
        let folded=&q[INITIAL_QUERY_BYTES..INITIAL_QUERY_BYTES+128];
        #[cfg(not(feature = "private-leaf-salts"))]
        let (leaf,path_offset)=(merkle::leaf_with_digest(hash,0x72,folded),INITIAL_QUERY_BYTES+128);
        #[cfg(feature = "private-leaf-salts")]
        let (leaf,path_offset)=(
            aspis_core::state_only_private_merkle::private_leaf_hash_with_digest(hash,0x72,folded,q[INITIAL_QUERY_BYTES+128..INITIAL_QUERY_BYTES+160].try_into().unwrap()),
            INITIAL_QUERY_BYTES+160,
        );
        if !merkle_path(hash,v.folded_root.unwrap(),u/4,leaf,&q[path_offset..]) {return Err(Error::Merkle);}
    }
    mark(obs,Phase::Merkle(i));
    let dots=crate::fast_dots::four_dots(q,g);#[cfg(feature="detail-phases")]mark(obs,Phase::QueryPart(i,0));for s in 0..4 {crate::trace::value(9,4*i+s,dots[s]);}
    let inverse=geometry.for_query(i);
    let mut folded=circle_fold_with_inverses(p.alpha[0],dots,inverse);crate::trace::value(10,2*i,folded);#[cfg(feature="detail-phases")]mark(obs,Phase::QueryPart(i,1));
    if p.variant.folds()==2 {
        let values=core::array::from_fn(|s|field(&q[INITIAL_QUERY_BYTES..],s));
        if folded!=values[u%4] {return Err(Error::Query);}
        folded=line_fold_with_inverses(p.alpha[1],values,inverse);crate::trace::value(10,2*i+1,folded);
    }
    #[cfg(feature="detail-phases")]mark(obs,Phase::QueryPart(i,2));
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
    let mut dot=crate::fast_pairing::EbyKDot::new();
    for (j,w) in a.weights.iter().enumerate() {dot.push(field(v.final_message,j),*w).map_err(|_|Error::Parse)?;}
    let actual=dot.finish();
    crate::trace::value(17,0,actual);crate::trace::value(17,1,a.rhs);
    if a.next!=22||actual!=a.rhs {return Err(Error::Query);}
    mark(obs,Phase::Final);Ok(())
}

fn put(out:&mut Vec<u8>,x:E) {out.extend_from_slice(&x.to_le_bytes());}
fn put_k(out:&mut Vec<u8>,x:K) {let mut b=[0;16];x.write_le_bytes(&mut b);out.extend_from_slice(&b);}
pub fn checkpoint<H:Digest32>(p:&Prepared,a:&Accumulator,proof:&[u8],public:&[u8],hash:H)->Vec<u8> {
    let mut out=Vec::with_capacity(checkpoint_size(p.variant));
    out.extend_from_slice(b"R1P2CKP2");out.extend_from_slice(&[p.variant.tag(),a.next as u8,1,0,0,0,0,0]);
    out.extend_from_slice(&hash.digest(&[proof]));out.extend_from_slice(&hash.digest(&[public]));out.extend_from_slice(&p.state);
    for root in &p.roots {out.extend_from_slice(root);}
    for x in [p.gamma,p.kappa,p.alpha[0],p.alpha[1]] {put(&mut out,x);}
    put_k(&mut out,p.rho);
    for q in p.queries {out.extend_from_slice(&q.to_le_bytes());}
    for x in p.semantic_alpha {let mut b=[0;16];x.write_le_bytes(&mut b);out.extend_from_slice(&b);}
    for z in p.z {for x in [z.x,z.y] {let mut b=[0;16];x.write_le_bytes(&mut b);out.extend_from_slice(&b);}}
    for x in [p.claim,a.rhs] {put(&mut out,x);}
    put_k(&mut out,a.power);
    for &x in &a.weights {put_k(&mut out,x);}
    let sum=hash.digest(&[b"UNPROVED:R1:checkpoint",&out]);out.extend_from_slice(&sum);
    assert_eq!(out.len(),checkpoint_size(p.variant));out
}
struct Reader<'a>{bytes:&'a[u8],at:usize}
impl<'a> Reader<'a>{
    fn raw<const N:usize>(&mut self)->[u8;N] {let b=self.bytes[self.at..self.at+N].try_into().unwrap();self.at+=N;b}
    fn e(&mut self)->Result<E,Error>{E::from_le_bytes(&self.raw::<32>()).ok_or(Error::Checkpoint)}
    fn k(&mut self)->Result<K,Error>{K::from_le_bytes(&self.raw::<16>()).ok_or(Error::Checkpoint)}
}
#[inline(never)]
pub fn resume<H:Digest32>(bytes:&[u8],proof:&[u8],public:&[u8],v:Variant,hash:H)->Result<(Box<Prepared>,Accumulator),Error> {
    if bytes.len()!=checkpoint_size(v)||&bytes[..8]!=b"R1P2CKP2"||bytes[8]!=v.tag()||bytes[9]>22||bytes[10]!=1||bytes[11..16].iter().any(|&b|b!=0) {return Err(Error::Checkpoint);}
    let end=bytes.len()-32;
    if bytes[16..48]!=hash.digest(&[proof])||bytes[48..80]!=hash.digest(&[public])||bytes[end..]!=hash.digest(&[b"UNPROVED:R1:checkpoint",&bytes[..end]]) {return Err(Error::Checkpoint);}
    let mut r=Reader{bytes,at:80};let state=r.raw();let roots=[r.raw(),r.raw()];
    let gamma=r.e()?;let kappa=r.e()?;let alpha=[r.e()?,r.e()?];let rho=r.k()?;
    let queries=core::array::from_fn(|_|u32::from_le_bytes(r.raw()));
    for (i,q) in queries.iter().enumerate(){if *q>=1<<18||queries[..i].contains(q){return Err(Error::Checkpoint);}}
    let mut semantic_alpha=[K::ZERO;10];for x in &mut semantic_alpha {*x=r.k()?;}
    let z=[SecureCirclePoint{x:r.k()?,y:r.k()?},SecureCirclePoint{x:r.k()?,y:r.k()?}];
    let claim=r.e()?;let rhs=r.e()?;let power=r.k()?;
    let mut weights=aspis_core::r0::heap::filled(v.final_len(),K::ZERO).map_err(|_|Error::Allocation)?;
    for x in &mut weights {*x=r.k()?;}
    if r.at!=end {return Err(Error::Checkpoint);}
    Ok((Box::new(Prepared{variant:v,roots,gamma,kappa,alpha,rho,queries,semantic_alpha,z,claim,state}),Accumulator{weights,rhs,power,next:bytes[9] as usize}))
}
#[inline(never)]
fn tx1_finish<H:Digest32>(v:View<'_>,p:Box<Prepared>,mut a:Accumulator,g:[E;29],public_bytes:&[u8],proof:&[u8],k:usize,hash:H,obs:Observer)->Result<Vec<u8>,Error> {
    let geometry=QueryGeometry::for_range(&p.queries,0,k)?;
    while a.next<k {query_with_geometry(&v,&p,&mut a,&g,hash,obs,&geometry)?;}
    let bytes=checkpoint(&p,&a,proof,public_bytes,hash);mark(obs,Phase::CheckpointWrite);Ok(bytes)
}

#[inline(never)]
fn tx1_prepare<H:Digest32>(public:Public<'_>,v:&View<'_>,hash:H,obs:Observer,g:&mut [E;29])->Result<(Box<[[K;29];3]>,Box<Prepared>),Error> {
    let sem=crate::r1_semantic::verify_observed(public,v.semantic,hash,obs).map_err(|_|Error::Semantic)?;mark(obs,Phase::Semantic);
    let p=Prepared::new(&sem,v,hash,g)?;
    Ok((sem.claims,p))
}

#[inline(never)]
pub fn tx1<H:Digest32>(public:Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize,hash:H,obs:Observer)->Result<Vec<u8>,Error> {
    if k>22 {return Err(Error::Parse);}
    let v=View::parse(proof)?;mark(obs,Phase::Parsed);
    let mut g=[E::ZERO;29];
    let (_semantic_claims,p)=tx1_prepare(public,&v,hash,obs,&mut g)?;let a=Accumulator::new(v.variant)?;mark(obs,Phase::Prepare);
    tx1_finish(v,p,a,g,public_bytes,proof,k,hash,obs)
}
/// Complete strict verification of an R1 proof and its checkpoint.
///
/// Runtime precondition: the checkpoint must be an authentic output of `tx1`
/// for the proof and public statement bound by its hashes. `resume` recomputes
/// both hashes from the current buffers: changes reject except for a collision.
/// The checkpoint checksum is an unkeyed hash, not a MAC, and
/// does not establish checkpoint provenance by itself. This strict entrypoint
/// repeats the full canonical scan of proof fields and query values.
#[inline(never)]
pub fn tx2<H:Digest32>(public_bytes:&[u8],proof:&[u8],checkpoint:&[u8],hash:H,obs:Observer)->Result<(),Error> {
    let v=View::parse(proof)?;mark(obs,Phase::Parsed);
    let (p,mut a)=resume(checkpoint,proof,public_bytes,v.variant,hash)?;let g=powers::<29>(p.gamma);mark(obs,Phase::CheckpointRead);
    let geometry=QueryGeometry::for_range(&p.queries,a.next,22)?;
    while a.next<22 {query_with_geometry(&v,&p,&mut a,&g,hash,obs,&geometry)?;}
    finish_relation(&v,&p,&a,obs)
}

/// Complete verification using proof bytes whose checkpoint provenance was
/// established by the caller.
///
/// Runtime precondition: the checkpoint must be an authentic output of `tx1`
/// for the proof and public statement bound by its hashes. This is also a
/// precondition of strict `tx2`. `resume` recomputes the proof/public hashes;
/// changed buffers reject except for a collision. The checkpoint checksum is
/// an unkeyed hash, not a MAC, and does not
/// establish checkpoint provenance by itself. This entrypoint only skips the
/// redundant per-field canonical scan of the proof; use strict `tx2` when that
/// scan is required.
#[inline(never)]
pub fn tx2_authenticated<H:Digest32>(public_bytes:&[u8],proof:&[u8],checkpoint:&[u8],hash:H,obs:Observer)->Result<(),Error> {
    let v=View::parse_shape(proof)?;mark(obs,Phase::Parsed);
    let (p,mut a)=resume(checkpoint,proof,public_bytes,v.variant,hash)?;let g=powers::<29>(p.gamma);mark(obs,Phase::CheckpointRead);
    let geometry=QueryGeometry::for_range(&p.queries,a.next,22)?;
    while a.next<22 {query_with_geometry(&v,&p,&mut a,&g,hash,obs,&geometry)?;}
    finish_relation(&v,&p,&a,obs)
}

#[cfg(test)]
mod query_geometry_tests {
    use super::*;
    use aspis_core::field::{CM31,QM31,P};

    fn next(state:&mut u64)->u64 {
        *state=state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut value=*state;
        value=(value^(value>>30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        value=(value^(value>>27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        value^(value>>31)
    }
    fn random_m31(state:&mut u64)->M31 {M31((next(state)%u64::from(P)) as u32)}
    fn random_e(state:&mut u64)->E {
        let mut scalar=||random_m31(state);
        let mut k=||QM31{c0:CM31{a:scalar(),b:scalar()},c1:CM31{a:scalar(),b:scalar()}};
        E::new(k(),k())
    }
    fn queries()->[u32;22] {core::array::from_fn(|i|((i*7919+12345)%262144) as u32)}

    #[test]
    fn batched_geometry_inverses_match_individual_inverses_for_ranges() {
        let queries=queries();
        for (start,end) in [(0,0),(0,1),(0,7),(7,22),(0,22),(5,19)] {
            let geometry=QueryGeometry::for_range(&queries,start,end).unwrap();
            assert_eq!(geometry.start,start);
            assert_eq!(geometry.inverses.len(),end-start);
            for index in start..end {
                let u=queries[index] as usize;
                let point=crate::fast_domain::fibre_point(domain::FibreIndex::new(u).unwrap());
                let line_x=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4).unwrap());
                let line_y=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4+3).unwrap());
                let line_z=line_x.mul(line_x).double().sub(M31::ONE);
                assert_eq!(*geometry.for_query(index),[point.x.inv(),point.y.inv(),line_x.inv(),line_y.inv(),line_z.inv()]);
            }
        }
    }

    #[test]
    fn batched_circle_and_line_folds_match_independent_reference() {
        let queries=queries();
        let geometry=QueryGeometry::for_range(&queries,0,22).unwrap();
        let mut state=0x243f_6a88_85a3_08d3;
        let max=E::from_limbs([P-1;8]).unwrap();
        for index in 0..22 {
            for case in 0..8 {
                let alpha=match case%4 {0=>E::ZERO,1=>E::ONE,2=>max,_=>random_e(&mut state)};
                let values=core::array::from_fn(|slot|match (case+slot)%4 {0=>E::ZERO,1=>E::ONE,2=>max,_=>random_e(&mut state)});
                let inverse=geometry.for_query(index);
                assert_eq!(circle_fold_with_inverses(alpha,values,inverse),circle_fold(alpha,queries[index] as usize,values),"circle index {index}, case {case}");
                assert_eq!(line_fold_with_inverses(alpha,values,inverse),line_fold(alpha,queries[index] as usize/4,values),"line index {index}, case {case}");
            }
        }
    }
}
