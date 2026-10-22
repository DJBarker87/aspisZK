#![allow(dead_code,unexpected_cfgs)]
#![cfg_attr(kani,feature(stmt_expr_attributes,proc_macro_hygiene))]
extern crate alloc;
use aspis_core::field::{M31,CM31,QM31 as K,WideExact as E};
use aspis_r1_cost_probe::verifier::{self,Prepared,Accumulator,Error};
use aspis_r1_cost_probe::transport::Variant;
use aspis_core::Digest32;

// The spec rejects noncanonical limbs and states the physical LE limb order.
fn k_limbs(x:K)->[u32;4] {[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn k_from_limbs(x:[u32;4])->K {K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn word_spec(b:&[u8],at:usize)->u32 {
    (b[at] as u32)|((b[at+1] as u32)<<8)|((b[at+2] as u32)<<16)|((b[at+3] as u32)<<24)
}
fn decode_k_spec(b:&[u8])->Option<K> {
    let x=[word_spec(b,0),word_spec(b,4),word_spec(b,8),word_spec(b,12)];
    if x[0]>=0x7fffffff || x[1]>=0x7fffffff || x[2]>=0x7fffffff || x[3]>=0x7fffffff {None} else {Some(k_from_limbs(x))}
}
#[cfg_attr(kani,kani::requires(b.len()==16))]
#[cfg_attr(kani,kani::ensures(|r:&Option<[u32;4]>| *r==decode_k_spec(b).map(k_limbs)))]
fn decode_k_words(b:&[u8])->Option<[u32;4]> {K::from_le_bytes(b).map(k_limbs)}
fn decode_k(b:&[u8])->Option<K> {decode_k_words(b).map(k_from_limbs)}

fn encode_k_spec(x:K)->[u8;16] {
    let limbs=k_limbs(x);let mut out=[0;16];
    for i in 0..16 {out[i]=(limbs[i/4]>>(8*(i%4))) as u8;}
    out
}
#[cfg_attr(kani,kani::ensures(|r:&[u8;16]| *r==encode_k_spec(x)))]
fn encode_k(x:K)->[u8;16] {let mut out=[0;16];x.write_le_bytes(&mut out);out}

#[cfg_attr(kani,kani::requires(i<32))]
#[cfg_attr(kani,kani::ensures(|r:&u8| *r==((x.to_limbs()[i/4]>>(8*(i%4))) as u8)))]
fn encode_e_byte(x:E,i:usize)->u8 {x.to_le_bytes()[i]}

fn decode_e_spec(b:&[u8])->Option<E> {
    if b.len()!=32 {return None;}
    E::from_limbs([word_spec(b,0),word_spec(b,4),word_spec(b,8),word_spec(b,12),word_spec(b,16),word_spec(b,20),word_spec(b,24),word_spec(b,28)])
}
#[cfg_attr(kani,kani::requires(b.len()==32))]
#[cfg_attr(kani,kani::ensures(|r:&Option<[u32;8]>| *r==decode_e_spec(b).map(E::to_limbs)))]
fn decode_e_words(b:&[u8])->Option<[u32;8]> {E::from_le_bytes(b).map(E::to_limbs)}
fn decode_e(b:&[u8])->Option<E> {decode_e_words(b).map(|x|E::from_limbs(x).unwrap())}

// Sparse scalar reference: one physical byte, no materialized output vector.
fn k_byte(x:K,i:usize)->u8 {encode_k(x)[i]}
fn e_byte(x:E,i:usize)->u8 {(x.to_limbs()[i/4]>>(8*(i%4))) as u8}
fn body_byte(p:&Prepared,a:&Accumulator,hp:&[u8;32],hu:&[u8;32],i:usize)->u8 {
 if i<8 {b"R1P2CKP2"[i]}
 else if i<16 {[2,a.next as u8,1,0,0,0,0,0][i-8]}
 else if i<48 {hp[i-16]}
 else if i<80 {hu[i-48]}
 else if i<112 {p.state[i-80]}
 else if i<176 {p.roots[(i-112)/32][(i-112)%32]}
 else if i<304 {e_byte([p.gamma,p.kappa,p.alpha[0],p.alpha[1]][(i-176)/32],(i-176)%32)}
 else if i<320 {k_byte(p.rho,i-304)}
 else if i<408 {(p.queries[(i-320)/4]>>(8*((i-320)%4))) as u8}
 else if i<568 {k_byte(p.semantic_alpha[(i-408)/16],(i-408)%16)}
 else if i<632 {k_byte([p.z[0].x,p.z[0].y,p.z[1].x,p.z[1].y][(i-568)/16],(i-568)%16)}
 else if i<664 {e_byte(p.claim,i-632)}
 else if i<696 {e_byte(a.rhs,i-664)}
 else if i<712 {k_byte(a.power,i-696)}
 else {k_byte(a.weights[(i-712)/16],(i-712)%16)}
}

fn decode_body_reference(b:&[u8;1768])->Result<(Prepared,Accumulator),Error> {
    let read_e=|at:usize|decode_e(&b[at..at+32]).ok_or(Error::Checkpoint);
    let read_k=|at:usize|decode_k(&b[at..at+16]).ok_or(Error::Checkpoint);
    let mut queries=[0u32;22];
    for i in 0..22 {
        queries[i]=u32::from_le_bytes(b[320+4*i..324+4*i].try_into().unwrap());
        if queries[i]>=262144 {return Err(Error::Checkpoint);}
        for j in 0..i {if queries[j]==queries[i] {return Err(Error::Checkpoint);}}
    }
    let mut semantic_alpha=[K::ZERO;10];for i in 0..10 {semantic_alpha[i]=read_k(408+16*i)?;}
    let z=[aspis_core::circle::SecureCirclePoint{x:read_k(568)?,y:read_k(584)?},aspis_core::circle::SecureCirclePoint{x:read_k(600)?,y:read_k(616)?}];
    let p=Prepared{variant:Variant::S2,roots:[b[112..144].try_into().unwrap(),b[144..176].try_into().unwrap()],gamma:read_e(176)?,kappa:read_e(208)?,alpha:[read_e(240)?,read_e(272)?],rho:read_k(304)?,queries,semantic_alpha,z,claim:read_e(632)?,state:b[80..112].try_into().unwrap()};
    let rhs=read_e(664)?;let power=read_k(696)?;
    let mut weights=aspis_core::r0::heap::filled(64,K::ZERO).map_err(|_|Error::Allocation)?;
    for i in 0..64 {weights[i]=read_k(712+16*i)?;}
    Ok((p,Accumulator{weights,rhs,power,next:b[9] as usize}))
}

#[cfg(kani)] mod proofs {
use super::*;
use core::cell::Cell;
fn any_k()->K {k_from_limbs(kani::any())}
fn any_e()->E {let x:[u32;8]=kani::any();for i in 0..8 {kani::assume(x[i]<0x7fffffff);} E::from_limbs(x).unwrap()}
#[kani::proof_for_contract(decode_k_words)] #[kani::unwind(18)]
fn decode_k_contract() {let b:[u8;16]=kani::any();let _=decode_k_words(&b);}
#[kani::proof_for_contract(encode_k)] #[kani::unwind(18)]
fn encode_k_contract() {let _=encode_k(any_k());}
#[kani::proof_for_contract(encode_e_byte)] #[kani::unwind(10)]
fn encode_e_contract() {let i:usize=kani::any();kani::assume(i<32);let _=encode_e_byte(any_e(),i);}

#[kani::proof_for_contract(decode_e_words)] #[kani::unwind(34)]
fn decode_e_contract() {let b:[u8;32]=kani::any();let _=decode_e_words(&b);}

#[derive(Clone,Copy)]
struct WriterHash<'a> {step:&'a Cell<usize>,answers:[[u8;32];3],proof:&'a[u8],public:&'a[u8],prepared:&'a Prepared,accumulator:&'a Accumulator,index:usize}
impl Digest32 for WriterHash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
    let step=self.step.get();assert!(step<3);
    match step {
     0=>{assert_eq!(parts.len(),1);assert_eq!(parts[0],self.proof);},
     1=>{assert_eq!(parts.len(),1);assert_eq!(parts[0],self.public);},
     _=>{assert_eq!(parts.len(),2);assert_eq!(parts[0],b"UNPROVED:R1:checkpoint");assert_eq!(parts[1].len(),1736);assert_eq!(parts[1][self.index],body_byte(self.prepared,self.accumulator,&self.answers[0],&self.answers[1],self.index));}
    }
    self.step.set(step+1);self.answers[step]
 }
}
#[kani::proof]
#[kani::stub_verified(encode_k)]
#[kani::unwind(70)]
fn frozen_writer_exact_byte_and_reads() {
 let p=Prepared {variant:Variant::S2,roots:kani::any(),gamma:any_e(),kappa:any_e(),alpha:[any_e(),any_e()],rho:any_k(),queries:kani::any(),semantic_alpha:core::array::from_fn(|_|any_k()),z:core::array::from_fn(|_|aspis_core::circle::SecureCirclePoint{x:any_k(),y:any_k()}),claim:any_e(),state:kani::any()};
 let a=Accumulator{weights:(0..64).map(|_|any_k()).collect(),rhs:any_e(),power:any_k(),next:10};
 let proof:[u8;3]=kani::any();let public:[u8;5]=kani::any();
 let answers:[[u8;32];3]=kani::any();
 let i:usize=kani::any();kani::assume(i<1736);let j:usize=kani::any();kani::assume(j<1768);
 let step=Cell::new(0);let hash=WriterHash{step:&step,answers,proof:&proof,public:&public,prepared:&p,accumulator:&a,index:i};
 let got=verifier::checkpoint(&p,&a,&proof,&public,hash);
 assert_eq!(step.get(),3);assert_eq!(got.len(),1768);
 assert_eq!(got[j],if j<1736 {body_byte(&p,&a,&answers[0],&answers[1],j)} else {answers[2][j-1736]});
}
}


#[cfg(kani)] mod sections {
 use super::*;
 use alloc::vec::Vec;
 use aspis_r1_cost_probe::verifier::Error;
 include!("reader-source.rs");
 include!("section-proofs.rs");
}
