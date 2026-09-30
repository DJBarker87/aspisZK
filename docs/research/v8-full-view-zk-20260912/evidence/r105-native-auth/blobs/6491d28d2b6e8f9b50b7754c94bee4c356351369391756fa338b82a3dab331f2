//! Separate higher-arity AUTHENTICATION EXPERIMENT, not the selected protocol.
//! Digest width and SHA-256 retained; domains 0x14/0x18 are version candidates.
use corelib::{HashFn,v7_merkle208::{V7Digest,truncate_sha256_v7}};
type Entry=(u32,V7Digest,V7Digest);
pub(super) fn verify<const A:usize>(hash:HashFn,roots:(&V7Digest,&V7Digest),depth:u32,
    entries:&[Entry],nodes:(&[u8],&[u8]))->bool {
    if !matches!(A,2|4|8) || depth>=32 {return false;}
    let bits=A.trailing_zeros();let total=depth*bits;
    if total>=32 || entries.is_empty() || entries.len()>22 || nodes.0.len()%26!=0
        || nodes.0.len()!=nodes.1.len() {return false;}
    if entries.windows(2).any(|p|p[0].0>=p[1].0)
        || entries.last().unwrap().0 >= (1u32<<total) {return false;}
    let tag=if A==2{0x11}else if A==4{0x14}else{0x18};
    let mut level=entries.to_vec();let mut at=0usize;
    for _ in 0..depth {
        let mut read=0usize;let mut write=0usize;
        while read<level.len(){
            let parent=level[read].0>>bits;let start=parent<<bits;
            let mut p1:[&[u8];9]=[&[];9];let mut p2=p1;
            p1[0]=core::slice::from_ref(&tag);p2[0]=p1[0];
            for slot in 0..A {
                if read<level.len() && level[read].0==start+slot as u32 {
                    p1[slot+1]=&level[read].1;p2[slot+1]=&level[read].2;read+=1;
                }else{
                    if at+26>nodes.0.len(){return false;}
                    p1[slot+1]=&nodes.0[at..at+26];p2[slot+1]=&nodes.1[at..at+26];at+=26;
                }
            }
            let h1=truncate_sha256_v7(hash(&p1[..A+1]));
            let h2=truncate_sha256_v7(hash(&p2[..A+1]));
            // Each group consumes at least one entry; only past children change.
            level[write]=(parent,h1,h2);write+=1;
        }
        level.truncate(write);
    }
    at==nodes.0.len() && level.len()==1 && level[0].0==0
        && level[0].1==*roots.0 && level[0].2==*roots.1
}

pub(super) fn parse_and_verify(hash:HashFn,bytes:&[u8])->bool{
    if bytes.len()<72 || &bytes[..8]!=b"R101AUTH" || bytes[10..12]!=[0,0] {return false;}
    let arity=bytes[8];let depth=u32::from(bytes[9]);
    let count=u32::from_le_bytes(bytes[12..16].try_into().unwrap())as usize;
    let nodes=u32::from_le_bytes(bytes[16..20].try_into().unwrap())as usize;
    if count==0 || count>22 || nodes>22*31*7 || bytes.len()!=72+56*count+52*nodes {return false;}
    let root1=bytes[20..46].try_into().unwrap();let root2=bytes[46..72].try_into().unwrap();
    let entries:Vec<_>=bytes[72..72+56*count].chunks_exact(56).map(|b|
        (u32::from_le_bytes(b[..4].try_into().unwrap()),b[4..30].try_into().unwrap(),b[30..56].try_into().unwrap())).collect();
    let start=72+56*count;let frontiers=(&bytes[start..start+26*nodes],&bytes[start+26*nodes..]);
    match arity {
        2=>crate::r95_merkle::verify(hash,(&root1,&root2),depth,&entries,frontiers),
        4=>verify::<4>(hash,(&root1,&root2),depth,&entries,frontiers),
        8=>verify::<8>(hash,(&root1,&root2),depth,&entries,frontiers),
        _=>false
    }
}
