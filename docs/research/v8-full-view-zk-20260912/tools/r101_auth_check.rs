//! Independent full-tree oracle and PUBLIC synthetic authentication fixtures.
extern crate aspis_core as corelib;
use corelib::v7_merkle208::V7Digest as D;
use sha2::{Sha256,Digest};
use std::{collections::BTreeSet,path::Path};
mod r95_merkle;
mod r101_merkle;
fn hash(p:&[&[u8]])->[u8;32]{let mut h=Sha256::new();for x in p{h.update(x);}h.finalize().into()}
fn parent(a:usize,children:&[D])->D{
    let tag=if a==2{0x11}else if a==4{0x14}else{0x18};
    let mut bytes=vec![tag];for c in children{bytes.extend_from_slice(c);}
    hash(&[&bytes])[..26].try_into().unwrap()
}
fn tree(a:usize,depth:u32,channel:u8)->Vec<Vec<D>>{
    let size=a.pow(depth);let mut result=vec![(0..size).map(|i|
        hash(&[b"R101/public/synthetic/leaf",&[channel],&(i as u32).to_le_bytes()])[..26].try_into().unwrap()).collect::<Vec<D>>()];
    while result.last().unwrap().len()>1 {
        let next=result.last().unwrap().chunks_exact(a).map(|c|parent(a,c)).collect();result.push(next);
    }
    result
}
fn fixture(a:usize,t1:&[Vec<D>],t2:&[Vec<D>],ids:&[u32])->Vec<u8>{
    let mut frontier=[vec![],vec![]];let mut positions:BTreeSet<_>=ids.iter().copied().collect();
    for level in 0..t1.len()-1 {
        let parents:BTreeSet<_>=positions.iter().map(|x|*x/a as u32).collect();
        for &p in &parents {for slot in 0..a as u32 {
            let child=p*a as u32+slot;if !positions.contains(&child){
                frontier[0].extend_from_slice(&t1[level][child as usize]);frontier[1].extend_from_slice(&t2[level][child as usize]);
            }
        }}
        positions=parents;
    }
    let mut out=b"R101AUTH".to_vec();out.extend([a as u8,(t1.len()-1)as u8,0,0]);
    out.extend_from_slice(&(ids.len()as u32).to_le_bytes());out.extend_from_slice(&((frontier[0].len()/26)as u32).to_le_bytes());
    out.extend_from_slice(&t1.last().unwrap()[0]);out.extend_from_slice(&t2.last().unwrap()[0]);
    for &id in ids{out.extend_from_slice(&id.to_le_bytes());out.extend_from_slice(&t1[0][id as usize]);out.extend_from_slice(&t2[0][id as usize]);}
    out.extend_from_slice(&frontier[0]);out.extend_from_slice(&frontier[1]);out
}
fn ids(size:usize,n:usize,seed:usize)->Vec<u32>{
    let mut out=BTreeSet::new();let mut r=seed as u64+1;
    while out.len()<n{r^=r<<13;r^=r>>7;r^=r<<17;out.insert((r%size as u64)as u32);}
    out.into_iter().collect()
}
fn main(){
    let args:Vec<_>=std::env::args().collect();let dest=Path::new(&args[1]);assert!(!dest.exists());std::fs::create_dir_all(dest).unwrap();
    let mut honest=0;let mut negatives=0;
    for a in [2usize,4,8]{for depth in 0..=3 {
        let t1=tree(a,depth,1);let t2=tree(a,depth,2);let size=t1[0].len();
        for case in 0..64 {
            let q=ids(size,1+case%size.min(22),case+depth as usize*71);let proof=fixture(a,&t1,&t2,&q);
            assert!(r101_merkle::parse_and_verify(hash,&proof));honest+=1;
            for bad in [0usize,8,10,20,46,72,76,102] {
                let mut b=proof.clone();b[bad]^=255;assert!(!r101_merkle::parse_and_verify(hash,&b));negatives+=1;
            }
            let mut b=proof.clone();b.push(0);assert!(!r101_merkle::parse_and_verify(hash,&b));negatives+=1;
            assert!(!r101_merkle::parse_and_verify(hash,&proof[..proof.len()-1]));negatives+=1;
            if q.len()>1 {let mut b=proof.clone();let i=b[72..76].to_vec();b[128..132].copy_from_slice(&i);assert!(!r101_merkle::parse_and_verify(hash,&b));negatives+=1;}
        }
    }}
    for a in [2usize,4,8]{
        let depth=18/a.trailing_zeros();let t1=tree(a,depth,1);let t2=tree(a,depth,2);
        for world in 0..2 {
            let q=ids(1<<18,22,0x101+world);let proof=fixture(a,&t1,&t2,&q);
            assert!(r101_merkle::parse_and_verify(hash,&proof));
            let folder=dest.join(format!("a{a}-world{world}"));std::fs::create_dir(&folder).unwrap();
            std::fs::write(folder.join("proof-1.bin"),&proof).unwrap();
            std::fs::write(folder.join("public.bin"),b"R101-auth-only-public-fixture").unwrap();
            std::fs::write(folder.join("transition.bin"),b"R101-auth-only-no-settlement").unwrap();
            std::fs::write(folder.join("binding.bin"),[0u8;32]).unwrap();
            println!("R101_FIXTURE arity={a} depth={depth} world={world} bytes={} nodes={} queries={q:?} synthetic_public_leaves=true",proof.len(),u32::from_le_bytes(proof[16..20].try_into().unwrap()));
        }
    }
    println!("R101_AUTH honest={honest} malformed={negatives} independent_full_trees=true actual_proofs=false");
}
