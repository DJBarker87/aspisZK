//! Isolated complete RELATION suffix, not a payment verifier or deployment.
//! Real canonical body, SHA transcript, two Merkle frontiers and quotient
//! openings. No verifier function receives a full quotient coefficient vector.
//! Public ordinary weights/claim come from the outer semantic verifier, whose
//! Aspis-specific construction is NOT supplied by this research callback.
extern crate aspis_core as corelib;
extern crate sha2;
use corelib::{field::{QM31 as K,CM31,M31},transcript::{Transcript,label},sumcheck::{WeightAccumulator,evaluate,polynomial_for_extension},
    circle::{SecureCirclePoint as Point},v6_onefold::gamma_combine_v6_packed_layer0,
    state_only_spend_query::StateOnlySpendQueryPowers,v7_merkle208::*};
use sha2::{Sha256,Digest};
const FIXED:usize=697; const Q:usize=22; const REC:usize=621; const HEAD:usize=FIXED*16+52+24;
const V8_COMPONENT_OOD_VECTOR:u8=62; // pinned V8 branch transcript.rs
#[derive(Debug,PartialEq)] enum Error {Length,Canonical,Sampler,Shape,Authentication,Terminal,Domain}
fn hash(parts:&[&[u8]])->[u8;32] {let mut h=Sha256::new();for p in parts {h.update(p);}h.finalize().into()}
fn sc(x:u32)->K {K::from_cm31(CM31::from_m31(M31(x)))}
fn bytes(v:&[K])->Vec<u8> {let mut b=vec![0;v.len()*16];for(i,v)in v.iter().enumerate(){v.write_le_bytes(&mut b[i*16..i*16+16]);}b}
fn dot(a:&[K],b:&[K])->K {a.iter().zip(b).fold(K::ZERO,|s,(a,b)|s.add(a.mul(*b)))}
fn primal(v:&[K],a:K)->Vec<K>{v.chunks_exact(4).map(|v|v[0].add(a.mul(v[1].add(a.mul(v[2].add(a.mul(v[3]))))))).collect()}
fn image_terminal(t:K,b:K,c:K,a:[K;4])->K {
    a[1].mul(a[2]).mul(a[3]).mul(t.mul(a[0]).add(t.square().mul(b.mul(a[0].square()).sub(c.mul(a[0].square().mul(a[0])))))).mul_m31(M31(8388608))
}
fn compact(sent:&[K],claim:K)->[K;7]{[sent[0],sent[1],sent[2],sent[3],claim.half().half().sub(sent[0]),sent[4],sent[5]]}
fn absorb_round(t:&mut Transcript,r:usize,p:&[K;7]){let mut b=vec![r as u8];b.extend(bytes(&[p[0],p[1],p[2],p[3],p[5],p[6]]));t.absorb(label::V6_COMPACT_RELATION_ROUND,&b);}
fn sample(t:&mut Transcript,nonzero:bool)->Result<K,Error>{if nonzero {t.challenge_nonzero_qm31()}else{t.challenge_qm31()}.map_err(|_|Error::Sampler)}
struct Wire<'a>{v:Vec<K>,roots:([u8;26],[u8;26]),nonces:&'a[u8],records:&'a[u8],frontiers:(&'a[u8],&'a[u8])}
fn parse(b:&[u8])->Result<Wire<'_>,Error>{
    if b.len()<HEAD+Q*REC || b.len()>40282 || (b.len()-HEAD-Q*REC)%52!=0{return Err(Error::Length);}
    let v=b[..FIXED*16].chunks_exact(16).map(|x|K::from_le_bytes(x).ok_or(Error::Canonical)).collect::<Result<Vec<_>,_>>()?;
    let n=(b.len()-HEAD-Q*REC)/2;
    Ok(Wire{v,roots:(b[FIXED*16..FIXED*16+26].try_into().unwrap(),b[FIXED*16+26..FIXED*16+52].try_into().unwrap()),
        nonces:&b[FIXED*16+52..HEAD],records:&b[HEAD..HEAD+Q*REC],frontiers:(&b[HEAD+Q*REC..HEAD+Q*REC+n],&b[HEAD+Q*REC+n..])})
}
// The wrapper is deliberately a distinct research transcript. It binds C1
// before lambda/chi and C2 afterwards; the semantic prefix here is opaque.
// It does NOT claim to run the payment zerocheck or its deployment preamble.
fn before_ood(w:&Wire<'_>,statement:&[u8;32],hashfn:corelib::HashFn)->Result<Transcript,Error> {
    let mut t=Transcript::new(hashfn);t.absorb(label::PROFILE,b"AV8/relation-callback/v1");t.absorb(label::STATEMENT,statement);
    t.absorb(label::ROOT,&w.roots.0);let _=sample(&mut t,false)?;let _=sample(&mut t,false)?;
    t.absorb(label::SECOND_PHASE_ROOT,&w.roots.1);t.absorb(label::V6_POINT_CLAIMS,&bytes(&w.v[..358]));
    Ok(t)
}
struct Prefix {t:Transcript, points:[Point;2],gamma:K,abc:[K;3],iv:[K;2],use_x:bool,tau:K}
fn freeze(mut t:Transcript,w:&Wire<'_>,ordinary:&[K],claim:K)->Result<Prefix,Error>{
    let s=t.challenge_secure_circle_point().map_err(|_|Error::Sampler)?;
    let mut record=vec![0];record.extend(bytes(&w.v[359..388]));t.absorb(V8_COMPONENT_OOD_VECTOR,&record);
    let mut second=None;for _ in 0..3 {let p=t.challenge_secure_circle_point().map_err(|_|Error::Sampler)?;if p!=s {second=Some(p);break;}}
    let z=second.ok_or(Error::Sampler)?;let mut record=vec![1];record.extend(bytes(&w.v[388..417]));t.absorb(V8_COMPONENT_OOD_VECTOR,&record);
    t.absorb(label::M31_PAYMENT_BATCH_POW_NONCE,&w.nonces[..8]);let gamma=sample(&mut t,true)?;
    t.absorb(label::V6_INACTIVE_CLAIM,&bytes(&w.v[358..359]));let _kappa=sample(&mut t,true)?;
    let batch=|v:&[K]|{let mut g=K::ONE;v.iter().fold(K::ZERO,|a,v|{let r=a.add(g.mul(*v));g=g.mul(gamma);r})};
    let use_x=s.x!=z.x;let h0=if use_x{s.x}else{s.y};let h1=if use_x{z.x}else{z.y};
    let slope=batch(&w.v[359..388]).sub(batch(&w.v[388..417])).mul(h0.sub(h1).try_inv().ok_or(Error::Domain)?);
    let iv=[batch(&w.v[359..388]).sub(slope.mul(h0)),slope];
    let abc=[s.x.mul(z.y).sub(s.y.mul(z.x)),s.y.sub(z.y),z.x.sub(s.x)];
    // Freeze the public ordinary relation AFTER gamma/chord and BEFORE tau.
    // No caller mutation/response callback is possible inside this boundary.
    // Dense public-input binding costs a 16,384-byte hash input, not wire bytes.
    t.absorb(label::PROFILE,&bytes(ordinary));t.absorb(label::CLAIM,&bytes(&[claim]));
    t.absorb(label::PROFILE,b"aspis-v8-image-gate-v1");let tau=sample(&mut t,true)?;
    Ok(Prefix{t,points:[s,z],gamma,abc,iv,use_x,tau})
}
fn query_schedule(p:&mut Prefix,finals:&[K],nonces:&[u8])->Result<(Vec<u32>,K),Error>{
    p.t.absorb(label::V6_FINAL256,&bytes(finals));p.t.absorb(label::GRIND_NONCE,&nonces[16..24]);
    let q=p.t.challenge_queries_without_replacement(22,1<<18,64).map_err(|_|Error::Sampler)?;
    p.t.absorb(label::PROFILE,b"AV8/query-batch/v1");let rho=sample(&mut p.t,true)?;Ok((q,rho))
}
fn opened_values(w:&Wire<'_>,p:&Prefix,queries:&[u32],alpha:K,hashfn:corelib::HashFn)->Result<(Vec<K>,Vec<M31>),Error>{
    let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,queries).map_err(|_|Error::Domain)?;
    let powers=StateOnlySpendQueryPowers::new(p.gamma);let mut entries=vec![];let mut values=vec![];let mut xs=vec![];
    for (i,base) in pts.iter().enumerate(){
        let r=&w.records[i*REC..(i+1)*REC];let salt:&[u8;32]=r[589..621].try_into().unwrap();
        let combined=gamma_combine_v6_packed_layer0(&r[..403],&r[403..589],&powers).map_err(|_|Error::Canonical)?;
        entries.push((queries[i],private_leaf_hash_v7(hashfn,V7_C1_TREE_TAG,&r[..403],salt),private_leaf_hash_v7(hashfn,V7_C2_TREE_TAG,&r[403..589],salt)));
        let x=sc(base.x.0);let y=sc(base.y.0);let points=[(x,y),(x,y.neg()),(x.neg(),y.neg()),(x.neg(),y)];
        let mut qv=[K::ZERO;4];for j in 0..4{let(x,y)=points[j];let h=if p.use_x{x}else{y};
            qv[j]=combined[j].sub(p.iv[0].add(p.iv[1].mul(h))).mul(p.abc[0].add(p.abc[1].mul(x)).add(p.abc[2].mul(y)).try_inv().ok_or(Error::Domain)?);}
        if base.x==M31::ZERO || base.y==M31::ZERO{return Err(Error::Domain);}
        values.push(corelib::field::qm31_circle_to_line_fold4(qv,alpha,base.x.double().inv(),base.y.double().inv()));xs.push(base.x.mul(base.x).double().sub(M31::ONE));
    }
    entries.sort_by_key(|x|x.0);
    if !verify_two_minimal_subtrees_v7_bytes(hashfn,(&w.roots.0,&w.roots.1),18,&entries,w.frontiers,&mut vec![],&mut vec![]){return Err(Error::Authentication);}
    Ok((values,xs))
}
fn inject(weights:&mut WeightAccumulator,c:&mut K,values:&[K],xs:&[M31],rho:K)->Result<K,Error>{
    let mut power=rho;let scales:Vec<K>=(0..values.len()).map(|_|{let a=power;power=power.mul(rho);a}).collect();
    weights.add_line_m31_batch(&scales,xs).map_err(|_|Error::Shape)?;let inc=dot(&scales,values);*c=c.add(inc);Ok(inc)
}
/// Complete callback endpoint: all compact rounds, canonical fields, actual
/// authenticated virtual quotient checks and carried-image terminal. No Q input.
fn verify_relation(body:&[u8],statement:[u8;32],ordinary:Vec<K>,claim:K,hashfn:corelib::HashFn)->Result<(),Error>{
    if ordinary.len()!=1024{return Err(Error::Shape);}let w=parse(body)?;
    let mut p=freeze(before_ood(&w,&statement,hashfn)?,&w,&ordinary,claim)?;
    let mut weights=WeightAccumulator::empty(10);weights.add_dense(ordinary).map_err(|_|Error::Shape)?;
    let mut c=claim;let mut a=[K::ZERO;4];let first=compact(&w.v[417..423],c);absorb_round(&mut p.t,0,&first);
    let mut work=vec![0];work.extend_from_slice(&w.nonces[8..16]);p.t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE,&work);
    a[0]=sample(&mut p.t,false)?;c=evaluate(&first,a[0]);weights.fold_deferred_relation_arity4(a[0]);
    let mut f=w.v[441..697].to_vec();let(queries,rho)=query_schedule(&mut p,&f,w.nonces)?;
    let(values,xs)=opened_values(&w,&p,&queries,a[0],hashfn)?;let inc=inject(&mut weights,&mut c,&values,&xs,rho)?;
    p.t.absorb(label::PROFILE,&bytes(&[inc]));
    for r in 1..4{let poly=compact(&w.v[417+r*6..423+r*6],c);absorb_round(&mut p.t,r,&poly);
        a[r]=sample(&mut p.t,false)?;c=evaluate(&poly,a[r]);weights.fold_deferred_relation_arity4(a[r]);f=primal(&f,a[r]);}
    let terminal=(0..4).fold(K::ZERO,|v,i|v.add(weights.weight_at(i as u32).mul(f[i]))).add(image_terminal(p.tau,p.abc[1],p.abc[2],a).mul(f[3]));
    if terminal!=c{return Err(Error::Terminal);}Ok(())
}

#[path="relation_callback_fixtures.rs"] mod fixtures;
#[cfg(not(any(v8_inactive_binding,v8_radius_boundary)))]
fn main(){fixtures::run();}
#[cfg(any(v8_inactive_binding,v8_radius_boundary))]
#[path="inactive_row_binding.rs"] mod inactive_binding;
#[cfg(v8_inactive_binding)]
fn main(){inactive_binding::run();}
#[cfg(v8_radius_boundary)]
#[path="radius_boundary.rs"] mod radius_boundary;
#[cfg(v8_radius_boundary)]
fn main(){radius_boundary::run();}
