//! UNPROVED R1 COST PROBE. Two-transaction verifier shape; no production use.
use aspis_core::r0::CodeField;
use alloc::{boxed::Box,vec::Vec};
use aspis_core::{Digest32,field::{WideExact as E,QM31 as K,M31},circle::SecureCirclePoint,r0::{domain,merkle}};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
use crate::{transport::Variant,weights::{Weights,field,powers,QUARTER},transcript::Transcript};

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
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation,
    /// Host prover only (LOG D38.3): this attempt's challenges fail the public
    /// P_R1 check. Carries no challenge and no conjunct.
    #[cfg(feature="prover")] Rejected,
    /// Host prover only (D38.3): all N = 8 attempts were rejected; nothing is published.
    #[cfg(feature="prover")] AttemptsExhausted,
    /// Host prover only: the operating-system entropy source failed.
    #[cfg(feature="prover")] Entropy }
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
    /// Length of the retired eight-way stored proof for `v` (124,343 bytes for
    /// S2). A layout figure only: the adopted stored length is `PROOF_BYTES`.
    pub fn eight_way_proof_bytes(v:Variant)->usize {HEADER+SEMANTIC_BYTES+29*32+32+7*32+if v.folds()==2 {32+7*32}else{0}+v.final_len()*32+22*(INITIAL_QUERY_BYTES+if v.folds()==2 {SECOND_QUERY_BYTES}else{0})}
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
struct QueryGeometry { start:usize, inverses:Vec<[M31;5]>, line_z:Vec<M31> }

#[inline(always)]
fn batch_prefix_products(flat:&[M31])->(Vec<M31>,M31) {
    let mut prefixes=Vec::with_capacity(flat.len());
    let mut product=M31::ONE;
    let mut index=0;
    while index<flat.len() {
        let value=flat[index];
        prefixes.push(product);
        product=product.mul(value);
        index+=1;
    }
    (prefixes,product)
}

impl QueryGeometry {
    fn for_range(queries:&[u32;22],start:usize,end:usize)->Result<Self,Error> {
        if start>end||end>queries.len(){return Err(Error::Query);}
        let mut line_z_values=Vec::with_capacity(end-start);
        let mut flat=Vec::with_capacity((end-start)*5);
        for &query in &queries[start..end] {
            let u=query as usize;
            let fibre=domain::FibreIndex::new(u).map_err(|_|Error::Query)?;
            let domain::Point{x:circle_x,y:circle_y}=crate::fast_domain::fibre_point(fibre);
            let line_x=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4).map_err(|_|Error::Query)?);
            let line_y=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4+3).map_err(|_|Error::Query)?);
            let line_z=line_x.mul(line_x).double().sub(M31::ONE);
            let values=[circle_x,circle_y,line_x,line_y,line_z];
            if values.iter().any(|x|*x==M31::ZERO){return Err(Error::Query);}
            flat.extend_from_slice(&values);
            line_z_values.push(line_z);
        }
        if flat.is_empty(){return Ok(Self{start,inverses:Vec::new(),line_z:line_z_values});}
        // Standard prefix-product/backward batch inversion. The only `inv`
        // in this routine is applied to the product of all nonzero entries.
        let (prefixes,product)=batch_prefix_products(&flat);
        let mut suffix_inverse=product.inv();
        let mut flat_inverse=Vec::with_capacity(flat.len());
        flat_inverse.resize(flat.len(),M31::ZERO);
        for i in (0..flat.len()).rev() {
            flat_inverse[i]=suffix_inverse.mul(prefixes[i]);
            suffix_inverse=suffix_inverse.mul(flat[i]);
        }
        let inverses=(0..line_z_values.len()).map(|i|core::array::from_fn(|j|flat_inverse[5*i+j])).collect();
        Ok(Self{start,inverses,line_z:line_z_values})
    }
    #[inline(always)]
    #[cfg_attr(kani,kani::requires(self.start<=index && index-self.start<self.inverses.len()))]
    #[cfg_attr(kani,kani::ensures(|r| (core::ptr::eq(*r,NDI_verifier::reference::geometry_ref(&self.inverses,self.start,index))) != cfg!(NDI_invert_geometry)))]
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
/// Transaction-local residues. At a group boundary each limb is <2^34.
/// Four products add at most 4*(P-1)^2; adding the retained folded residue
/// still fits u64 because 4*(P-1)^2+2^34 < 2^64. Flush after each four queries.
struct BatchedWeights { raw:Vec<[u64;4]>, terms:usize }
impl BatchedWeights {
    fn new(weights:&[K])->Result<Self,Error> {
        let mut raw=aspis_core::r0::heap::filled(weights.len(),[0u64;4]).map_err(|_|Error::Allocation)?;
        let mut index=0;
        while index<weights.len() {
            let w=weights[index];
            raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];
            index+=1;
        }
        Ok(Self{raw,terms:0})
    }
    #[inline(always)]
    fn push(&mut self,index:usize,power:K,basis:M31) {
        let flush=self.terms&3==3;
        update_residue_row(&mut self.raw[index],power,basis,flush);
    }

    fn value(&self,index:usize)->K {
        let [a,b,c,d]=self.raw[index].map(M31::reduce_u64);
        K{c0:aspis_core::field::CM31{a,b},c1:aspis_core::field::CM31{a:c,b:d}}
    }
    fn finish(&self,weights:&mut[K]) {for (i,w) in weights.iter_mut().enumerate(){*w=self.value(i);}}
}


#[inline(always)]
fn residue_limb_at(row:&[u64;4],index:usize)->u64 {row[index]}
#[inline(always)]
fn power_limb_at(limbs:&[u32;4],index:usize)->u32 {limbs[index]}
#[inline(always)]
fn update_residue_row(row:&mut [u64;4],power:K,basis:M31,flush:bool) {
    let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
    for j in 0..4 {
        let old=residue_limb_at(row,j);
        let limb=power_limb_at(&limbs,j);
        row[j]=old+u64::from(limb)*u64::from(basis.0);
    }
    if flush {
        for limb in row {*limb=(*limb&0x7fff_ffff)+(*limb>>31);}
    }
}

#[inline(never)]
pub fn accumulate(p:&Prepared,a:&mut Accumulator,index:usize,value:E) {
    let mut node=crate::fast_domain::line_node(domain::FibreIndex::new(if p.variant.folds()==1 {index}else{index/4*4}).unwrap());
    if p.variant.folds()==2 {for _ in 0..2 {node=node.mul(node).double().sub(M31::ONE);}}
    accumulate_with_node(p,a,node,value,None)
}
#[inline(never)]
fn accumulate_with_node(p:&Prepared,a:&mut Accumulator,mut node:M31,value:E,mut pending:Option<&mut BatchedWeights>) {
    let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let mut n=1;
    while n<a.weights.len() {for j in 0..n {basis[n+j]=basis[j].mul(node);} node=node.mul(node).double().sub(M31::ONE);n*=2;}
    for j in 0..a.weights.len() {
        if let Some(weights)=pending.as_deref_mut() {
            weights.push(j,a.power,basis[j]);
            #[cfg(feature="prover")] {a.weights[j]=weights.value(j);}
        } else {a.weights[j]=a.weights[j].add(a.power.mul_m31(basis[j]));}
        crate::trace::value(12,a.next*a.weights.len()+j,E::from_qm31(a.weights[j]));
        crate::trace::value(13,a.next*a.weights.len()+j,E::from_m31(basis[j]));
    }
    if let Some(weights)=pending {weights.terms+=1;}
    a.rhs=a.rhs.add(value.mul_qm31(a.power));crate::trace::value(11,a.next,a.rhs);
    a.power=a.power.mul(p.rho);a.next+=1;
}


#[inline(always)]
fn basis_at(basis:&[M31;256],index:usize)->M31 {basis[index]}
#[inline(always)]
fn accumulated_weight_at(weights:&[K],index:usize)->K {weights[index]}

#[inline(never)]
fn accumulate_batched_with_node(p:&Prepared,a:&mut Accumulator,mut node:M31,value:E,weights:&mut BatchedWeights) {
    let width=a.weights.len();
    let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let mut n=1;
    while n<width {for j in 0..n {basis[n+j]=basis[j].mul(node);} node=node.mul(node).double().sub(M31::ONE);n*=2;}
    for j in 0..width {
        weights.push(j,a.power,basis_at(&basis,j));
        #[cfg(feature="prover")] {a.weights[j]=weights.value(j);}
        crate::trace::value(12,a.next*width+j,E::from_qm31(accumulated_weight_at(&a.weights,j)));
        crate::trace::value(13,a.next*width+j,E::from_m31(basis_at(&basis,j)));
    }
    weights.terms+=1;
    a.rhs=a.rhs.add(value.mul_qm31(a.power));crate::trace::value(11,a.next,a.rhs);
    a.power=a.power.mul(p.rho);a.next+=1;
}

pub fn polynomial(bytes:&[u8],x:E)->E {(0..7).rev().fold(E::ZERO,|a,i|a.mul(x).add(field(bytes,i)))}
fn finish_relation_round(poly:&[u8],alpha:E,mut claim:E,round:usize)->Result<E,Error> {
        let lhs=field(poly,0).add(field(poly,4));let rhs=claim.mul_m31(QUARTER);
        crate::trace::value(15,3*round,lhs);crate::trace::value(15,3*round+1,rhs);
        if lhs!=rhs {return Err(Error::Relation);}
        claim=polynomial(poly,alpha);crate::trace::value(15,3*round+2,claim);
    Ok(claim)
}

fn finish_query_dot(final_message:&[u8],weights:&[K])->Result<E,Error> {
    let mut dot=crate::fast_pairing::EbyKDot::new();
    let mut j=0;
    while j<weights.len() {dot.push(field(final_message,j),weights[j]).map_err(|_|Error::Parse)?;j+=1;}
    Ok(dot.finish())
}

#[inline(never)]
pub fn finish_relation(v:&View<'_>,p:&Prepared,a:&Accumulator,obs:Observer)->Result<(),Error> {
    let mut claim=p.claim;
    claim=finish_relation_round(v.round0,p.alpha[0],claim,0)?;
    if p.variant.folds()==2 {claim=finish_relation_round(v.round1,p.alpha[1],claim,1)?;}
    let weights=Weights::new(p.variant,&p.semantic_alpha,&p.z)?;
    let pair=weights.pair(&p.alpha[..p.variant.folds()],v.final_message,p.kappa)?;
    crate::trace::value(16,0,pair);crate::trace::value(16,1,claim);
    if pair!=claim {return Err(Error::Relation);}
    mark(obs,Phase::Relation);
    let actual=finish_query_dot(v.final_message,&a.weights)?;
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
    #[inline(always)]
    fn k(&mut self)->Result<K,Error>{K::from_le_bytes(&self.raw::<16>()).ok_or(Error::Checkpoint)}
}


#[inline(always)]
fn validate_checkpoint_queries(queries:&[u32;22])->Result<(),Error> {
    let mut i=0;
    while i<queries.len() {
        let q=queries[i];
        if q>=1<<18||queries[..i].contains(&q){return Err(Error::Checkpoint);}
        i+=1;
    }
    Ok(())
}

#[inline(always)]
fn read_checkpoint_weights(bytes:&[u8],mut at:usize,mut weights:Vec<K>)->Result<(Vec<K>,usize),Error> {
    for out in &mut weights {
        let mut reader=Reader{bytes,at};
        let value=reader.k()?;
        at=reader.at;
        *out=value;
    }
    Ok((weights,at))
}


#[inline(always)]
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

#[inline(never)]
pub fn resume<H:Digest32>(bytes:&[u8],proof:&[u8],public:&[u8],v:Variant,hash:H)->Result<(Box<Prepared>,Accumulator),Error> {
    if bytes.len()!=checkpoint_size(v)||&bytes[..8]!=b"R1P2CKP2"||bytes[8]!=v.tag()||bytes[9]>22||bytes[10]!=1||bytes[11..16].iter().any(|&b|b!=0) {return Err(Error::Checkpoint);}
    let end=bytes.len()-32;
    if bytes[16..48]!=hash.digest(&[proof])||bytes[48..80]!=hash.digest(&[public])||bytes[end..]!=hash.digest(&[b"UNPROVED:R1:checkpoint",&bytes[..end]]) {return Err(Error::Checkpoint);}
    let mut r=Reader{bytes,at:80};let state=r.raw();let roots=[r.raw(),r.raw()];
    let gamma=r.e()?;let kappa=r.e()?;let alpha=[r.e()?,r.e()?];let rho=r.k()?;
    let queries=[
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
        u32::from_le_bytes(r.raw()),
    ];
    validate_checkpoint_queries(&queries)?;
    let (semantic_alpha,at)=read_checkpoint_semantic_alpha(bytes,r.at)?;
    r.at=at;
    let z=[SecureCirclePoint{x:r.k()?,y:r.k()?},SecureCirclePoint{x:r.k()?,y:r.k()?}];
    let claim=r.e()?;let rhs=r.e()?;let power=r.k()?;
    let weights=aspis_core::r0::heap::filled(v.final_len(),K::ZERO).map_err(|_|Error::Allocation)?;
    let (weights,at)=read_checkpoint_weights(bytes,r.at,weights)?;
    if at!=end {return Err(Error::Checkpoint);}
    Ok((Box::new(Prepared{variant:v,roots,gamma,kappa,alpha,rho,queries,semantic_alpha,z,claim,state}),Accumulator{weights,rhs,power,next:bytes[9] as usize}))
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

#[cfg(test)]
mod batched_weight_tests {
    use super::*;
    #[test]
    fn bounded_rho_residues_match_all_canonical_prefixes() {
        let hi=M31(aspis_core::field::P-1);
        let max=K{c0:aspis_core::field::CM31{a:hi,b:hi},c1:aspis_core::field::CM31{a:hi,b:hi}};
        for power in [K::ZERO,K::ONE,max] {
            let mut reference=alloc::vec![max;64];let mut pending=BatchedWeights::new(&reference).unwrap();
            for _ in 0..22 {
                for j in 0..64 {
                    pending.push(j,power,hi);
                    reference[j]=reference[j].add(power.mul_m31(hi));
                    assert_eq!(pending.value(j),reference[j]);
                }
                pending.terms+=1;
            }
            let mut actual=alloc::vec![K::ZERO;64];pending.finish(&mut actual);assert_eq!(actual,reference);
        }
    }
}

// The adopted R1 verifier (PREREG-PROOF-SIZE-2, 2026-10-19): the compact
// binary-multiproof format of `crate::compact`. These are the only R1
// verification entrypoints of a default build.
#[path="candidate.rs"]
pub mod candidate;
pub use candidate::{parse_shape,tx1,tx2,tx2_authenticated};
/// The one stored proof length of the adopted format (57,607 bytes).
pub const PROOF_BYTES:usize=crate::compact::PROOF_BYTES;
/// The one stage-1 split of the adopted format (queries 0..10 in stage 1).
pub const SPLIT:usize=crate::compact::SPLIT;
const _:()=assert!(PROOF_BYTES==57_607&&SPLIT==10);

// AUDIT ONLY: the retired eight-way verifier, for differential evidence on
// saved eight-way fixtures. Never in a prover or SBF build (lib.rs guards).
#[cfg(feature="audit-eight-way")]
#[path="eight_way.rs"]
pub mod eight_way;

#[cfg(kani)] #[path="NDI_verifier.rs"] mod NDI_verifier;
