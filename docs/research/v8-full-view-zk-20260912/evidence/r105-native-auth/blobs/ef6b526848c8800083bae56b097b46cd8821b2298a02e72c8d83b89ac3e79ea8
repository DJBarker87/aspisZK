//! Prover/reference side of the separately versioned 8-way commitment profile.
//! Root remains at slot 18 in the existing prover container; only multiples of
//! three contain tree levels. No binary tree node is relabelled as an 8-way node.
use corelib::{HashFn,v7_merkle208::{V7Digest as D,truncate_sha256_v7}};
use std::collections::{BTreeMap,BTreeSet};
type Tree=Vec<Vec<D>>;
type Entry=(u32,D,D);
fn parent(hash:HashFn,children:&[D])->D {
    assert_eq!(children.len(),8);
    let mut bytes=[0u8;209];bytes[0]=0x18;
    for (i,c) in children.iter().enumerate(){bytes[1+26*i..27+26*i].copy_from_slice(c);}
    truncate_sha256_v7(hash(&[&bytes]))
}
pub(super) fn tree(hash:HashFn,leaves:Vec<D>)->Tree {
    assert_eq!(leaves.len(),1<<18);
    let mut t=vec![leaves];
    for level in 1..=18 {
        let row=if level%3==0{t[level-3].chunks_exact(8).map(|c|parent(hash,c)).collect()}else{vec![]};
        t.push(row);
    }
    t
}
pub(super) fn frontier(t:&Tree,queries:&[u32])->Vec<u8>{
    assert_eq!(t.len(),19);let mut nodes:BTreeSet<_>=queries.iter().copied().collect();let mut out=vec![];
    assert_eq!(nodes.len(),queries.len());
    for level in (0..18).step_by(3){
        let parents:BTreeSet<_>=nodes.iter().map(|p|*p/8).collect();
        for p in &parents{for slot in 0..8 {let j=p*8+slot;
            if !nodes.contains(&j){out.extend_from_slice(&t[level][j as usize]);}
        }}
        nodes=parents;
    }
    out
}
// Host differential implementation: maps and rebuilt levels, concatenated
// preimages. The fast verifier instead borrows slices and overwrites a frontier.
pub(super) fn verify_reference(hash:HashFn,roots:(&D,&D),depth:u32,entries:&[Entry],nodes:(&[u8],&[u8]))->bool{
    if depth>=11 || entries.is_empty() || entries.len()>22 || nodes.0.len()%26!=0 || nodes.0.len()!=nodes.1.len(){return false;}
    if entries.windows(2).any(|w|w[0].0>=w[1].0)||entries.last().unwrap().0>=1u32<<(3*depth){return false;}
    let mut level:BTreeMap<_,_>=entries.iter().map(|&(j,a,b)|(j,(a,b))).collect();let mut at=0;
    for _ in 0..depth {
        let parents:BTreeSet<_>=level.keys().map(|p|*p/8).collect();let mut next=BTreeMap::new();
        for p in parents {
            let mut first=Vec::new();let mut second=Vec::new();
            for child in 0..8 {
                if let Some(&(a,b))=level.get(&(p*8+child)){first.push(a);second.push(b);}
                else{
                    let(Some(a),Some(b))=(nodes.0.get(at..at+26),nodes.1.get(at..at+26))else{return false;};
                    first.push(a.try_into().unwrap());second.push(b.try_into().unwrap());at+=26;
                }
            }
            next.insert(p,(parent(hash,&first),parent(hash,&second)));
        }
        level=next;
    }
    at==nodes.0.len() && level.len()==1 && level.get(&0)==Some(&(*roots.0,*roots.1))
}
