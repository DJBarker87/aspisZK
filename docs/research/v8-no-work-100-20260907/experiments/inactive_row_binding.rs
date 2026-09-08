//! Research-only causal semantic + relation experiment. NOT pool settlement,
//! a selected production verifier, a deployment, or a complete FS certificate.
//! New hypothesis: aggregate ordinary equality implies row-zero binding.
use super::*;
extern crate aspis_statement as statement;
use statement::pool_v1::*;
use corelib::state_only_sumcheck::{begin_state_only_zerocheck,evaluate_state_only_polynomial};
use corelib::state_only_hiding::{begin_state_only_masked_sumcheck,state_only_explicit_g_mask_factor};
use std::collections::BTreeSet;

struct Public {transfer:PoolV1PrivateTransferPublicV1, withdrawal:PoolV1WithdrawalPublicV1, transition:PoolV1PairLatePublicStatementV1}
fn public()->Public {
    let zero=[M31::ZERO;8];let mut empty=[zero;21];empty[0]=pool_v1_tree_parent(&zero,&zero);
    for i in 1..21{empty[i]=pool_v1_tree_parent(&empty[i-1],&empty[i-1]);}
    let transfer=PoolV1PrivateTransferPublicV1{pool:[1;32],deployment_domain:[2;32],anchor_sequence:0,
        anchor_root:[M31(3);8],nullifier:[M31(4);8],asset_id:M31(5),recipient_commitment:[M31(6);8],change_commitment:[M31(7);8]};
    let withdrawal=PoolV1WithdrawalPublicV1{pool:[1;32],deployment_domain:[2;32],anchor_sequence:0,
        anchor_root:[M31(3);8],nullifier:[M31(4);8],asset_id:M31(5),amount:1,destination_token_account:[8;32],change_commitment:[M31(7);8]};
    let transition=PoolV1PairLatePublicStatementV1{
        live_snapshot:PoolV1PairLiveSnapshotV1{pool:[1;32],deployment_domain:[2;32],sequence:0,next_pair_index:0,current_root:empty[20],frontier:core::array::from_fn(|i|empty[i])},
        candidate_afterstate:PoolV1PairVerifiedAfterstateV1{next_pair_index:1,next_root:[M31(9);8],next_frontier:core::array::from_fn(|i|if i==0{[M31(10);8]}else{empty[i]})}};
    Public{transfer,withdrawal,transition}
}
pub(super) struct Semantic {pub(super) t:Transcript,pub(super) z:[K;10],lambda:K,chi:K,theta:K,zc:[K;10],mu:K,eta:K,claim:K}
pub(super) fn semantic(w:&Wire<'_>,seed:u32,shift:bool)->Result<Semantic,Error>{
    let mut t=Transcript::new(hash);
    t.absorb(label::PROFILE,if shift{b"AV8/semantic-row-shift/v1"}else{b"AV8/semantic-row-collision/v1"});
    // A synthetic public context, not the full deployment/account preamble.
    t.absorb(label::STATEMENT,&seed.to_le_bytes());t.absorb(label::ROOT,&w.roots.0);
    let lambda=sample(&mut t,false)?;let chi=sample(&mut t,false)?;
    t.absorb(label::SECOND_PHASE_ROOT,&w.roots.1);
    let batching=begin_state_only_zerocheck(&mut t).map_err(|_|Error::Sampler)?;
    let eta=begin_state_only_masked_sumcheck(&mut t,w.v[0]).map_err(|_|Error::Sampler)?;
    let mut z=[K::ZERO;10];let mut claim=w.v[0];
    for r in 0..10{
        let sent=&w.v[1+r*27..1+(r+1)*27];let mut poly=[K::ZERO;28];poly[0]=sent[0];poly[2..].copy_from_slice(&sent[1..]);
        let tail=poly[2..].iter().fold(poly[0].add(poly[0]),|a,v|a.add(*v));poly[1]=claim.sub(tail);
        assert_eq!(corelib::state_only_sumcheck::state_only_boundary_sum(&poly),claim);
        let mut framed=vec![r as u8];framed.extend(bytes(sent));t.absorb(label::V6_COMPACT_SEMANTIC_ROUND,&framed);
        z[r]=sample(&mut t,false)?;claim=evaluate_state_only_polynomial(&poly,z[r]);
    }
    // Kept separate so the prover can fill point claims AFTER semantic rounds.
    Ok(Semantic{t,z,lambda,chi,theta:batching.theta,zc:batching.zerocheck_point,mu:batching.mu,eta,claim})
}
fn terminal(public:&Public,w:&Wire<'_>,s:&Semantic,withdraw:bool)->K{
    let claims:[K;84]=core::array::from_fn(|i|w.v[271+29*(i/28)+i%28]);
    if withdraw {evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1(
        &public.withdrawal,&public.transition,&claims,&s.z,s.lambda,s.chi,s.theta,&s.zc,s.mu,s.eta).unwrap()}
    else {evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(
        &public.transfer,&public.transition,&claims,&s.z,s.lambda,s.chi,s.theta,&s.zc,s.mu,s.eta).unwrap()}
}
// Existing source uses one label for all three 29-column point rows.
pub(super) fn points_absorb(t:&mut Transcript,w:&Wire<'_>){t.absorb(label::V6_POINT_CLAIMS,&bytes(&w.v[271..358]));}
fn to_gamma(mut t:Transcript,w:&Wire<'_>)->Result<(Transcript,[Point;2],K),Error>{
    points_absorb(&mut t,w);
    let s=t.challenge_secure_circle_point().map_err(|_|Error::Sampler)?;
    let mut rec=vec![0];rec.extend(bytes(&w.v[359..388]));t.absorb(V8_COMPONENT_OOD_VECTOR,&rec);
    let mut second=None;for _ in 0..3{let z=t.challenge_secure_circle_point().map_err(|_|Error::Sampler)?;if z!=s{second=Some(z);break;}}
    let z=second.ok_or(Error::Sampler)?;let mut rec=vec![1];rec.extend(bytes(&w.v[388..417]));t.absorb(V8_COMPONENT_OOD_VECTOR,&rec);
    t.absorb(label::M31_PAYMENT_BATCH_POW_NONCE,&w.nonces[..8]);let gamma=sample(&mut t,true)?;
    Ok((t,[s,z],gamma))
}
fn edges(j:usize)->Vec<(usize,M31)>{let mut row=j;let mut bit=0;let mut s=M31::ONE;let mut out=vec![];
    while row&(1<<bit)!=0{row^=1<<bit;s=s.mul(corelib::field::M31_HALF);out.push((row,s));bit+=1;}out.push((row|(1<<bit),s));out}
fn xt(v:&[K],n:usize)->Vec<K>{(0..n).map(|j|edges(j).into_iter().fold(K::ZERO,|a,(r,s)|a.add(v[r].mul_m31(s)))).collect()}
// Literal previously tested chord transpose, now over the linked core type.
fn transpose(w:&[K],[a,b,c]:[K;3])->Vec<K>{let mut w=w.to_vec();w.resize(1028,K::ZERO);
    let wa:Vec<K>=w.chunks_exact(2).map(|v|v[0]).collect();let wb:Vec<K>=w.chunks_exact(2).map(|v|v[1]).collect();
    let xwa=xt(&wa,513);let xxwa=xt(&xwa,512);let xwb=xt(&wb,512);let mut out=vec![K::ZERO;1024];
    for j in 0..512{out[2*j]=a.mul(wa[j]).add(b.mul(xwa[j])).add(c.mul(wb[j]));out[2*j+1]=c.mul(wa[j].sub(xxwa[j])).add(a.mul(wb[j])).add(b.mul(xwb[j]));}out}
pub(super) fn prepare(s:Semantic,w:&Wire<'_>,shift:bool)->Result<(Prefix,Vec<K>,K,K),Error>{
    let(t,points,gamma)=to_gamma(s.t,w)?;let mut t=t;
    t.absorb(label::V6_INACTIVE_CLAIM,&bytes(&w.v[358..359]));let kappa=sample(&mut t,true)?;
    let k2=kappa.square();let scales=if shift{[kappa,k2,k2.mul(kappa)]}else{[K::ONE,kappa,k2]};
    let mut orig=WeightAccumulator::empty(10);
    for (r,point) in corelib::v6_transcript::v6_statement_points(&s.z).into_iter().enumerate(){orig.add_multilinear(scales[r],point.to_vec()).unwrap();}
    orig.add_grouped_64x16_binary_masks_deferred_prepared(pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1(),pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1()).unwrap();
    let batch=|v:&[K]|{let mut g=K::ONE;v.iter().fold(K::ZERO,|a,v|{let r=a.add(g.mul(*v));g=g.mul(gamma);r})};
    let mut claim=w.v[358];for r in 0..3{claim=claim.add(scales[r].mul(batch(&w.v[271+29*r..300+29*r])));}
    let [z0,z1]=points;let use_x=z0.x!=z1.x;let h0=if use_x{z0.x}else{z0.y};let h1=if use_x{z1.x}else{z1.y};
    let slope=batch(&w.v[359..388]).sub(batch(&w.v[388..417])).mul(h0.sub(h1).try_inv().ok_or(Error::Domain)?);
    let iv=[batch(&w.v[359..388]).sub(slope.mul(h0)),slope];let abc=[z0.x.mul(z1.y).sub(z0.y.mul(z1.x)),z0.y.sub(z1.y),z1.x.sub(z0.x)];
    let original:Vec<K>=(0..1024).map(|i|orig.weight_at(i)).collect();
    claim=claim.sub(iv[0].mul(original[0])).sub(iv[1].mul(original[if use_x{2}else{1}]));
    let ordinary=transpose(&original,abc);
    t.absorb(label::PROFILE,&bytes(&ordinary));t.absorb(label::CLAIM,&bytes(&[claim]));t.absorb(label::PROFILE,b"aspis-v8-image-gate-v1");let tau=sample(&mut t,true)?;
    Ok((Prefix{t,points,gamma,abc,iv,use_x,tau},ordinary,claim,kappa))
}
pub(super) fn relation(w:&Wire<'_>,mut p:Prefix,ordinary:Vec<K>,mut c:K)->Result<(),Error>{
    let mut weights=WeightAccumulator::empty(10);weights.add_dense(ordinary).unwrap();let mut a=[K::ZERO;4];
    let first=compact(&w.v[417..423],c);absorb_round(&mut p.t,0,&first);let mut work=vec![0];work.extend(&w.nonces[8..16]);p.t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE,&work);
    a[0]=sample(&mut p.t,false)?;c=evaluate(&first,a[0]);weights.fold_deferred_relation_arity4(a[0]);
    let mut f=w.v[441..697].to_vec();let(q,rho)=query_schedule(&mut p,&f,w.nonces)?;let(values,xs)=opened_values(w,&p,&q,a[0],hash)?;
    let inc=inject(&mut weights,&mut c,&values,&xs,rho)?;p.t.absorb(label::PROFILE,&bytes(&[inc]));
    for r in 1..4{let poly=compact(&w.v[417+r*6..423+r*6],c);absorb_round(&mut p.t,r,&poly);a[r]=sample(&mut p.t,false)?;c=evaluate(&poly,a[r]);weights.fold_deferred_relation_arity4(a[r]);f=primal(&f,a[r]);}
    let expected=(0..4).fold(K::ZERO,|c,i|c.add(weights.weight_at(i as u32).mul(f[i]))).add(image_terminal(p.tau,p.abc[1],p.abc[2],a).mul(f[3]));
    if expected==c{Ok(())}else{Err(Error::Terminal)}
}
fn verify(body:&[u8],seed:u32,shift:bool,withdraw:bool,public:&Public)->Result<(),Error>{let w=parse(body)?;let s=semantic(&w,seed,shift)?;
    if terminal(public,&w,&s,withdraw)!=s.claim{return Err(Error::Terminal);}let(p,weights,claim,_)=prepare(s,&w,shift)?;relation(&w,p,weights,claim)}
fn uniform_tree(tag:u8,width:usize)->Vec<[u8;26]>{let mut t=vec![private_leaf_hash_v7(hash,tag,&vec![0;width],&[0;32])];for i in 0..18{t.push(node_hash_v7(hash,&t[i],&t[i]));}t}
fn frontier(t:&[[u8;26]],q:&[u32])->Vec<u8>{let mut out=vec![];let mut ns:BTreeSet<u32>=q.iter().copied().collect();for h in 0..18{for i in &ns{if !ns.contains(&(i^1)){out.extend(t[h]);}}ns=ns.iter().map(|i|i>>1).collect();}out}
const CORRUPT:u32=17; // chosen before C2 commitment, not after queries
fn corrupt_record()->Vec<u8>{let mut r=vec![0;REC];for slot in 0..4{let bit=31*(32+4*slot);r[403+bit/8]|=1<<(bit%8);}r}
fn corrupt_chain(zero:&[[u8;26]])->Vec<[u8;26]>{let r=corrupt_record();let mut t=vec![private_leaf_hash_v7(hash,V7_C2_TREE_TAG,&r[403..589],&[0;32])];
    for h in 0..18{t.push(if CORRUPT>>h&1==0{node_hash_v7(hash,&t[h],&zero[h])}else{node_hash_v7(hash,&zero[h],&t[h])});}t}
fn corrupt_frontier(zero:&[[u8;26]],changed:&[[u8;26]],q:&[u32])->Vec<u8>{let mut out=vec![];let mut ns:BTreeSet<u32>=q.iter().copied().collect();
    for h in 0..18{for i in &ns{let sibling=i^1;if !ns.contains(&sibling){out.extend(if sibling==CORRUPT>>h{changed[h]}else{zero[h]});}}ns=ns.iter().map(|i|i>>1).collect();}out}
fn body(v:&[K],a:&[[u8;26]],b:&[[u8;26]],fa:&[u8],fb:&[u8])->Vec<u8>{let mut out=bytes(v);out.extend(a[18]);out.extend(b[18]);out.extend([0;24]);out.resize(HEAD+Q*REC,0);out.extend(fa);out.extend(fb);out}
fn build(seed:u32,shift:bool,withdraw:bool,nonpoly:bool,public:&Public)->(Vec<u8>,K){
    let a=uniform_tree(V7_C1_TREE_TAG,403);let bz=uniform_tree(V7_C2_TREE_TAG,186);let b=if nonpoly{corrupt_chain(&bz)}else{bz.clone()};let mut v=vec![K::ZERO;697];
    let stub=body(&v,&a,&b,&[],&[]);let w=parse(&stub).unwrap();let s=semantic(&w,seed,shift).unwrap();let initial_terminal=terminal(public,&w,&s,withdraw);assert_ne!(initial_terminal,K::ZERO);
    let factor=state_only_explicit_g_mask_factor(&s.z);let forged=s.claim.sub(initial_terminal).mul(factor.try_inv().unwrap());assert_ne!(forged,K::ZERO);v[271+27]=forged;
    let stub=body(&v,&a,&b,&[],&[]);let w=parse(&stub).unwrap();let s=semantic(&w,seed,shift).unwrap();assert_eq!(terminal(public,&w,&s,withdraw),s.claim);
    let(_,_,gamma)=to_gamma(s.t,&w).unwrap();v[358]=gamma.pow(27).mul(forged).neg();
    let stub=body(&v,&a,&b,&[],&[]);let w=parse(&stub).unwrap();let s=semantic(&w,seed,shift).unwrap();let(mut p,_,claim,kappa)=prepare(s,&w,shift).unwrap();
    assert_eq!(p.iv,[K::ZERO;2]);if !shift{assert_eq!(claim,K::ZERO);}else{assert_eq!(claim,kappa.sub(K::ONE).mul(gamma.pow(27)).mul(forged));}
    let first=compact(&v[417..423],claim);absorb_round(&mut p.t,0,&first);p.t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE,&[0;9]);let alpha=sample(&mut p.t,false).unwrap();
    let(q,_)=query_schedule(&mut p,&v[441..697],&[0;24]).unwrap();let fa=frontier(&a,&q);let fb=if nonpoly{corrupt_frontier(&bz,&b,&q)}else{frontier(&b,&q)};
    // The predetermined seeds happen to avoid 17; no retries/search are used.
    if nonpoly{assert!(!q.contains(&CORRUPT));
        // Separate arithmetic/authentication probe deliberately opens 17.
        // This is NOT substituted for the actual transcript's query schedule.
        let forced:Vec<u32>=(0..22).collect();let fa=frontier(&a,&forced);let fb=corrupt_frontier(&bz,&b,&forced);
        let mut probe=body(&v,&a,&b,&fa,&fb);probe[HEAD+17*REC..HEAD+18*REC].copy_from_slice(&corrupt_record());
        let(values,_)=opened_values(&parse(&probe).unwrap(),&p,&forced,alpha,hash).unwrap();assert_ne!(values[17],K::ZERO);
        assert!(values.iter().enumerate().all(|(i,v)|i==17||*v==K::ZERO));
    }
    (body(&v,&a,&b,&fa,&fb),forged)
}
pub fn run(){let public=public();let mut accepted=0;let mut rejected=0;let mut max=0;
    for seed in 1..=8{for withdraw in [false,true]{for nonpoly in [false,true]{for shift in [false,true]{let(b,g)=build(seed,shift,withdraw,nonpoly,&public);max=max.max(b.len());assert!(b.len()<=40282);
        let result=verify(&b,seed,shift,withdraw,&public);if shift{assert_eq!(result,Err(Error::Terminal));rejected+=1;}else{assert_eq!(result,Ok(()));accepted+=1;}
        assert_ne!(g,K::ZERO);
    }}}}
    println!("PASS {accepted} unshifted semantic+image+relation suffixes accepted with false G(z); {rejected} shifted controls rejected; max body {max}");
    println!("Half the cases commit all-zero words; half commit D=1 on the four slots of fibre 17 and zero elsewhere (a non-polynomial word). OOD vectors, anchor, image residuals and final are zero; G(z) claim is nonzero. No witness or search used. NOT a complete production/pool transaction result.");
}
