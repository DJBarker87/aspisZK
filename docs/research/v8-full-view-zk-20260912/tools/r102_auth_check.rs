extern crate aspis_core as corelib;
use corelib::v7_merkle208::V7Digest as D;
use sha2::{Digest,Sha256};
mod r95_merkle;
mod r101_merkle;
mod r102_tree;
fn hash(p:&[&[u8]])->[u8;32]{let mut h=Sha256::new();for x in p{h.update(x);}h.finalize().into()}
fn main(){
    let trees=core::array::from_fn::<_,2,_>(|k|r102_tree::tree(hash,(0..1u32<<18).map(|j|
        hash(&[b"R102/public/authentication/control",&[k as u8],&j.to_le_bytes()])[..26].try_into().unwrap()).collect()));
    let roots=(&trees[0][18][0],&trees[1][18][0]);let mut state=0x1025abfed88u64;let mut count=0;
    for case in 0..512{
        let mut ids=std::collections::BTreeSet::new();
        while ids.len()<1+case%22{state^=state<<13;state^=state>>7;state^=state<<17;ids.insert((state&262143)as u32);}
        let ids:Vec<_>=ids.into_iter().collect();
        let entries:Vec<_>=ids.iter().map(|&i|(i,trees[0][0][i as usize],trees[1][0][i as usize])).collect();
        let a=r102_tree::frontier(&trees[0],&ids);let b=r102_tree::frontier(&trees[1],&ids);
        assert!(a.len()<=658*26 && a.len()==b.len());
        let compare=|entries:&[(u32,D,D)],a:&[u8],b:&[u8],roots:(&D,&D)|{
            let old=r102_tree::verify_reference(hash,roots,6,entries,(a,b));
            assert_eq!(r101_merkle::verify::<8>(hash,roots,6,entries,(a,b)),old);old
        };
        assert!(compare(&entries,&a,&b,roots));count+=1;
        for bad in 0..entries.len(){let mut e=entries.clone();e[bad].1[case%26]^=1;assert!(!compare(&e,&a,&b,roots));count+=1;}
        for offset in (0..a.len()).step_by(131){let mut bad=a.clone();bad[offset]^=1;assert!(!compare(&entries,&bad,&b,roots));count+=1;}
        assert!(!compare(&entries,&a[..a.len()-26],&b[..b.len()-26],roots));count+=1;
        let mut aa=a.clone();let mut bb=b.clone();aa.extend([0;26]);bb.extend([0;26]);
        assert!(!compare(&entries,&aa,&bb,roots));count+=1;
    }
    // Exact worst-frontier recurrence: at each next level at most 22 parents,
    // and at most the number of nodes in that level. It is attained here.
    let ids:Vec<u32>=(0..22).map(|j|j*3*4096).collect();
    assert_eq!(r102_tree::frontier(&trees[0],&ids).len(),658*26);
    println!("R102_AUTH source_prover_trees=2 query_schedules=512 differential_cases={count} max_frontier=658 attained=true checks_retained=true");
}
