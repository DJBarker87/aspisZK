//! Isolated complete RELATION suffix, not a payment verifier or deployment.
//! Real canonical body, SHA transcript, two Merkle frontiers and quotient
//! openings. No verifier function receives a full quotient coefficient vector.
//! Public ordinary weights/claim come from the outer semantic verifier, whose
//! Aspis-specific construction is NOT supplied by this research callback.
extern crate aspis_core as corelib;
#[cfg(not(v8_performance_sbf))]
extern crate sha2;
use corelib::{field::{QM31 as K,CM31,M31},transcript::{Transcript,label},sumcheck::{WeightAccumulator,evaluate,polynomial_for_extension},
    circle::{SecureCirclePoint as Point},v6_onefold::gamma_combine_v6_packed_layer0,
    state_only_spend_query::StateOnlySpendQueryPowers,v7_merkle208::*};
#[cfg(not(v8_performance_sbf))]
use sha2::{Sha256,Digest};
const FIXED:usize=697; const Q:usize=22; const REC:usize=621; const HEAD:usize=FIXED*16+52+24;
const V8_COMPONENT_OOD_VECTOR:u8=62; // pinned V8 branch transcript.rs
#[cfg(any(v8_leaf_record,test))]
#[path="leaf_record.rs"] mod leaf_record;
#[cfg(any(v8_auth_order,test))]
#[path="auth_order.rs"] mod auth_order;
#[cfg(any(v8_chord_norm,test))]
#[path="chord_norm.rs"] mod chord_norm;
#[cfg(any(v8_circle_norm,test))]
#[path="circle_norm.rs"] mod circle_norm;
#[cfg(v8_quotient_fused)]
#[path="quotient_fold.rs"] mod quotient_fold;
#[cfg(v8_affine_primal)]
#[path="affine_primal.rs"] mod affine_primal;
#[cfg(v8_gamma_wrap)]
#[path="query_arithmetic.rs"] mod query_arithmetic;
#[derive(Debug,PartialEq)] enum Error {Length,Canonical,Sampler,Shape,Authentication,Terminal,Domain}
#[cfg(not(v8_performance_sbf))]
fn hash(parts:&[&[u8]])->[u8;32] {let mut h=Sha256::new();for p in parts {h.update(p);}let digest=h.finalize().into();
    #[cfg(v8_query_graph)] query_graph::record(parts);
    digest}
#[cfg(v8_performance_sbf)]
fn hash(parts:&[&[u8]])->[u8;32] {solana_program::hash::hashv(parts).to_bytes()}
fn sc(x:u32)->K {K::from_cm31(CM31::from_m31(M31(x)))}
fn bytes(v:&[K])->Vec<u8> {let mut b=vec![0;v.len()*16];for(i,v)in v.iter().enumerate(){v.write_le_bytes(&mut b[i*16..i*16+16]);}b}
fn dot(a:&[K],b:&[K])->K {a.iter().zip(b).fold(K::ZERO,|s,(a,b)|s.add(a.mul(*b)))}
fn primal_reference(v:&[K],a:K)->Vec<K>{v.chunks_exact(4).map(|v|v[0].add(a.mul(v[1].add(a.mul(v[2].add(a.mul(v[3]))))))).collect()}
#[cfg(not(v8_query_kernels))]
fn primal(v:&[K],a:K)->Vec<K>{primal_reference(v,a)}

fn tower_inverse_k(values:&[K])->Result<Vec<K>,Error>{
    if values.is_empty() || values.iter().any(|v|*v==K::ZERO){return Err(Error::Domain);}
    let norms:Vec<CM31>=values.iter().map(|v|{
        let b=v.c1.square();
        let rb=CM31::new(b.a.double().sub(b.b),b.a.add(b.b.double()));
        v.c0.square().sub(rb)
    }).collect();
    let norms_m:Vec<M31>=norms.iter().map(|n|n.a.mul(n.a).add(n.b.mul(n.b))).collect();
    let inv=batch_inverse_m(&norms_m)?;
    Ok(values.iter().zip(norms).zip(inv).map(|((v,n),d)|{
        let ni=CM31::new(n.a.mul(d),n.b.neg().mul(d));
        K{c0:v.c0.mul(ni),c1:v.c1.neg().mul(ni)}
    }).collect())
}
#[cfg(all(v8_query_kernels,not(v8_affine_primal)))]
fn primal(v:&[K],a:K)->Vec<K>{
    use corelib::field::{PreparedQm31Multiplier as P,qm31_sum_products3_prepared};
    let a2=a.square();let ps=[P::new(a),P::new(a2),P::new(a2.mul(a))];
    let out:Vec<K>=v.chunks_exact(4).map(|c|c[0].add(qm31_sum_products3_prepared(&ps,&[c[1],c[2],c[3]]))).collect();
    #[cfg(not(v8_performance_sbf))]
    assert_eq!(out,primal_reference(v,a));
    out
}
#[cfg(v8_affine_primal)]
fn primal(v:&[K],a:K)->Vec<K>{affine_primal::fold(v,a)}

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
fn opened_values_reference(w:&Wire<'_>,p:&Prefix,queries:&[u32],alpha:K,hashfn:corelib::HashFn)->Result<(Vec<K>,Vec<M31>),Error>{
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
fn query_checkpoint(name:&str){
    #[cfg(all(v8_performance_sbf,v8_fine_profile))]
    performance_verifier::checkpoint(name);
    #[cfg(not(all(v8_performance_sbf,v8_fine_profile)))] let _=name;
}
fn batch_inverse_k(values:&[K])->Result<Vec<K>,Error>{
    if values.is_empty() || values.iter().any(|x|*x==K::ZERO){return Err(Error::Domain);}
    let mut prefix=Vec::with_capacity(values.len());prefix.push(values[0]);
    for x in &values[1..]{prefix.push(prefix.last().unwrap().mul(*x));}
    let mut inv=prefix.last().unwrap().try_inv().ok_or(Error::Domain)?;
    let mut out=vec![K::ZERO;values.len()];
    for i in (1..values.len()).rev(){out[i]=prefix[i-1].mul(inv);inv=inv.mul(values[i]);}
    out[0]=inv;Ok(out)
}
fn batch_inverse_m(values:&[M31])->Result<Vec<M31>,Error>{
    if values.is_empty() || values.iter().any(|x|*x==M31::ZERO){return Err(Error::Domain);}
    let mut prefix=Vec::with_capacity(values.len());prefix.push(values[0]);
    for x in &values[1..]{prefix.push(prefix.last().unwrap().mul(*x));}
    let mut inv=prefix.last().unwrap().inv();let mut out=vec![M31::ZERO;values.len()];
    for i in (1..values.len()).rev(){out[i]=prefix[i-1].mul(inv);inv=inv.mul(values[i]);}out[0]=inv;Ok(out)
}
#[inline(never)]
fn opened_values(w:&Wire<'_>,p:&Prefix,queries:&[u32],alpha:K,hashfn:corelib::HashFn)->Result<(Vec<K>,Vec<M31>),Error>{
    opened_values_prepared(w,p,queries,alpha,hashfn,None)
}
#[inline(never)]
fn opened_values_prepared(w:&Wire<'_>,p:&Prefix,queries:&[u32],alpha:K,hashfn:corelib::HashFn,prepared:Option<&StateOnlySpendQueryPowers>)->Result<(Vec<K>,Vec<M31>),Error>{
    #[cfg(v8_circle_norm)] let selected_points=circle_norm::Selected::new(queries)?;
    #[cfg(v8_circle_norm)] let pts=selected_points.points();
    #[cfg(not(v8_circle_norm))]
    let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,queries).map_err(|_|Error::Domain)?;
    query_checkpoint("v8:points");
    let owned;
    let powers=match prepared{Some(p)=>p,None=>{owned=StateOnlySpendQueryPowers::new(p.gamma);&owned}};
    let mut combined=Vec::with_capacity(queries.len());
    for i in 0..queries.len(){
        let r=&w.records[i*REC..(i+1)*REC];
        #[cfg(not(v8_gamma_wrap))]
        combined.push(gamma_combine_v6_packed_layer0(&r[..403],&r[403..589],&powers).map_err(|_|Error::Canonical)?);
        #[cfg(v8_gamma_wrap)]
        combined.push(query_arithmetic::gamma(&r[..403],&r[403..589],&powers)?);
    }
    query_checkpoint("v8:canonical-gamma");
    #[cfg(not(v8_auth_order))]
    let entries={
    let mut entries=Vec::with_capacity(queries.len());
    for (i,&id) in queries.iter().enumerate(){
        let r=&w.records[i*REC..(i+1)*REC];let salt:&[u8;32]=r[589..621].try_into().unwrap();
        #[cfg(not(v8_leaf_record))]
        entries.push((id,private_leaf_hash_v7(hashfn,V7_C1_TREE_TAG,&r[..403],salt),private_leaf_hash_v7(hashfn,V7_C2_TREE_TAG,&r[403..589],salt)));
        #[cfg(v8_leaf_record)]
        entries.push((id,private_leaf_hash_v7(hashfn,V7_C1_TREE_TAG,&r[..403],salt),leaf_record::c2(hashfn,r)));
    }
    query_checkpoint("v8:leaf-hashes");
    entries.sort_by_key(|x|x.0);
    entries};
    #[cfg(v8_auth_order)]
    let entries=auth_order::entries(w.records,queries,hashfn)?;
    #[cfg(v8_auth_order)] query_checkpoint("v8:ordered-leaf-hashes");
    if !verify_two_minimal_subtrees_v7_bytes(hashfn,(&w.roots.0,&w.roots.1),18,&entries,w.frontiers,&mut vec![],&mut vec![]){return Err(Error::Authentication);}
    query_checkpoint("v8:internal-auth");
    let mut denoms=Vec::with_capacity(4*queries.len());let mut numerators=Vec::with_capacity(4*queries.len());
    let mut base_denoms=Vec::with_capacity(2*queries.len());let mut xs=Vec::with_capacity(queries.len());
    for (i,base) in pts.iter().enumerate(){
        if base.x==M31::ZERO || base.y==M31::ZERO{return Err(Error::Domain);}
        base_denoms.extend([base.x.double(),base.y.double()]);
        xs.push(base.x.mul(base.x).double().sub(M31::ONE));
        #[cfg(v8_query_shared)]
        let (bx,cy,delta)=(p.abc[1].mul_m31(base.x),p.abc[2].mul_m31(base.y),
            p.iv[1].mul_m31(if p.use_x{base.x}else{base.y}));
        for (j,(x,y)) in [(base.x,base.y),(base.x,base.y.neg()),(base.x.neg(),base.y.neg()),(base.x.neg(),base.y)].into_iter().enumerate(){
            // Same input/output field, preserve the reference generic products
            // for the first measured batch-control ladder.
            #[cfg(not(v8_query_kernels))] {
                let x=sc(x.0);let y=sc(y.0);
                denoms.push(p.abc[0].add(p.abc[1].mul(x)).add(p.abc[2].mul(y)));
                numerators.push(combined[i][j].sub(p.iv[0].add(p.iv[1].mul(if p.use_x{x}else{y}))));
            }
            #[cfg(all(v8_query_kernels,not(v8_query_shared)))] {
                denoms.push(p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y)));
                numerators.push(combined[i][j].sub(p.iv[0].add(p.iv[1].mul_m31(if p.use_x{x}else{y}))));
            }
            #[cfg(v8_query_shared)] {
                let dx=if j<2{bx}else{bx.neg()};
                let dy=if j==0||j==3{cy}else{cy.neg()};
                let same=if p.use_x{j<2}else{j==0||j==3};
                denoms.push(p.abc[0].add(dx).add(dy));
                numerators.push(combined[i][j].sub(p.iv[0].add(if same{delta}else{delta.neg()})));
            }
        }
    }
    query_checkpoint("v8:denominators");
    #[cfg(all(v8_tower_batch,not(v8_chord_norm)))] let inverses=tower_inverse_k(&denoms)?;
    #[cfg(all(v8_chord_norm,not(v8_circle_norm)))] let inverses=chord_norm::inverse(&denoms,p.abc,&pts)?;
    #[cfg(all(v8_circle_norm,not(v8_joined_inverse)))] let inverses=selected_points.inverse(&denoms,p.abc)?;
    #[cfg(all(v8_joined_inverse,not(v8_line_norm)))] let (inverses,joined_m_inverse)=selected_points.inverse_joined(&denoms,p.abc,&base_denoms)?;
    #[cfg(v8_line_norm)] let (inverses,joined_m_inverse)=selected_points.inverse_lines(&denoms,p.abc,&base_denoms,&xs)?;
    #[cfg(all(v8_batch_k,not(any(v8_tower_batch,v8_chord_norm))))] let inverses=batch_inverse_k(&denoms)?;
    #[cfg(not(any(v8_batch_k,v8_tower_batch,v8_chord_norm)))] let inverses=denoms.iter().map(|d|d.try_inv().ok_or(Error::Domain)).collect::<Result<Vec<_>,_>>()?;
    query_checkpoint("v8:qm-inverses");
    #[cfg(all(v8_batch_m,not(v8_joined_inverse)))] let base_inverse=batch_inverse_m(&base_denoms)?;
    #[cfg(all(v8_joined_inverse,not(v8_split_inverse)))] let base_inverse=&joined_m_inverse[denoms.len()..];
    #[cfg(v8_split_inverse)] let base_inverse=&joined_m_inverse[..];
    #[cfg(not(v8_batch_m))] let base_inverse:Vec<M31>=base_denoms.iter().map(|d|d.inv()).collect();
    query_checkpoint("v8:base-inverses");
    #[cfg(all(v8_query_shared,not(v8_quotient_fused)))]
    let prepared_alpha=[alpha,alpha.square()].map(corelib::field::PreparedQm31Multiplier::new);
    #[cfg(v8_quotient_fused)] let prepared_fold=quotient_fold::Prepared::new(alpha);
    let values=(0..queries.len()).map(|i|{
        let qv=core::array::from_fn(|j|numerators[4*i+j].mul(inverses[4*i+j]));
        #[cfg(not(v8_query_shared))]
        {corelib::field::qm31_circle_to_line_fold4(qv,alpha,base_inverse[2*i],base_inverse[2*i+1])}
        #[cfg(all(v8_query_shared,not(v8_quotient_fused)))]
        {
            let [v0,v1,v2,v3]=qv;
            let positive=v0.add(v1).half().add(prepared_alpha[0].mul(v0.sub(v1).mul_m31(base_inverse[2*i+1])));
            let negative=v2.add(v3).half().sub(prepared_alpha[0].mul(v2.sub(v3).mul_m31(base_inverse[2*i+1])));
            let folded=positive.add(negative).half().add(prepared_alpha[1].mul(positive.sub(negative).mul_m31(base_inverse[2*i])));
            #[cfg(not(v8_performance_sbf))]
            assert_eq!(folded,corelib::field::qm31_circle_to_line_fold4(qv,alpha,base_inverse[2*i],base_inverse[2*i+1]));
            folded
        }
        #[cfg(v8_quotient_fused)] {prepared_fold.fold(qv,base_inverse[2*i],base_inverse[2*i+1])}
    }).collect::<Vec<_>>();
    query_checkpoint("v8:quotient-folds");
    #[cfg(all(v8_structured,not(v8_performance_sbf)))]
    assert_eq!((values.clone(),xs.clone()),opened_values_reference(w,p,queries,alpha,hashfn)?,"query reference differential");
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

#[cfg(not(v8_performance_sbf))]
#[path="relation_callback_fixtures.rs"] mod fixtures;
#[cfg(not(any(v8_inactive_binding,v8_radius_boundary,v8_payment_extraction,v8_performance_sbf)))]
fn main(){fixtures::run();}
#[cfg(any(v8_inactive_binding,v8_radius_boundary,v8_payment_extraction,v8_performance_sbf))]
#[path="inactive_row_binding.rs"] mod inactive_binding;
#[cfg(v8_inactive_binding)]
fn main(){inactive_binding::run();}
#[cfg(v8_radius_boundary)]
#[path="radius_boundary.rs"] mod radius_boundary;
#[cfg(v8_radius_boundary)]
fn main(){radius_boundary::run();}
#[cfg(v8_payment_extraction)]
extern crate aspis_core;
#[cfg(v8_payment_extraction)]
extern crate aspis_statement;
#[cfg(v8_payment_extraction)]
extern crate zeroize;
#[cfg(v8_payment_extraction)]
#[path="payment_source_modules.rs"] mod payment_sources;
#[cfg(v8_payment_extraction)]
use payment_sources::{circle_candidate,circle_candidate_openings,state_only_hiding,state_only_zerocheck,state_only_entropy};
#[cfg(v8_payment_extraction)]
#[path="recovered_witness.rs"] mod witness_endpoint;
#[cfg(v8_payment_extraction)]
#[path="authenticated_c1.rs"] mod authenticated_c1;
#[cfg(v8_payment_extraction)]
#[path="payment_extraction.rs"] mod payment_extraction;
#[cfg(v8_query_graph)]
#[path="c1_query_graph.rs"] mod query_graph;
#[cfg(v8_c1_gao)]
#[path="c1_gao.rs"] mod c1_gao;
#[cfg(all(v8_payment_extraction,not(v8_graph_orders),not(v8_circle_coordinates),not(v8_gao_completeness),not(v8_performance)))]
fn main(){payment_extraction::run();}
#[cfg(v8_graph_orders)]
fn main(){query_graph::exhaustive_depth_two_query_orders();}
#[cfg(v8_circle_coordinates)]
#[path="source_coordinate_gate.rs"] mod source_coordinate_gate;
#[cfg(v8_circle_coordinates)]
fn main(){source_coordinate_gate::run();}
#[cfg(v8_gao_completeness)]
fn main(){c1_gao::completeness_controls();}
#[cfg(v8_performance)]
fn main(){payment_extraction::performance::run();}
#[cfg(any(v8_performance,v8_performance_sbf))]
#[path="performance_verifier.rs"]
pub mod performance_verifier;
