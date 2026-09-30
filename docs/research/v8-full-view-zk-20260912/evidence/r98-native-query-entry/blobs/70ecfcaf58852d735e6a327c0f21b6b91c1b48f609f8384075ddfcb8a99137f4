//! Internal one-buffer walk. Parent bytes, call order and checks are retained.
use corelib::v7_merkle208::{V7Digest,V7_MERKLE_DIGEST_BYTES,node_hash_v7};
type Entry=(u32,V7Digest,V7Digest);
pub(super) fn verify(hash:corelib::HashFn,roots:(&V7Digest,&V7Digest),depth:u32,
    entries:&[Entry],nodes:(&[u8],&[u8]))->bool {
    if entries.is_empty() || depth>=32 || nodes.0.len()%26!=0 || nodes.1.len()%26!=0
        || nodes.0.len()!=nodes.1.len() {return false;}
    if entries.windows(2).any(|p|p[0].0>=p[1].0)
        || entries.last().unwrap().0 >= (1u32<<depth) {return false;}
    let mut level=entries.to_vec();let mut node_pos=0usize;
    for _ in 0..depth {
        let mut read=0usize;let mut write=0usize;
        while read<level.len() {
            let (position,ref c1,ref c2)=level[read];
            let parent=if position&1==0 && read+1<level.len() && level[read+1].0==position+1 {
                let (_,ref right1,ref right2)=level[read+1];
                read+=2;
                (node_hash_v7(hash,c1,right1),node_hash_v7(hash,c2,right2))
            }else{
                if node_pos+V7_MERKLE_DIGEST_BYTES>nodes.0.len(){return false;}
                let right1:&V7Digest=nodes.0[node_pos..node_pos+26].try_into().unwrap();
                let right2:&V7Digest=nodes.1[node_pos..node_pos+26].try_into().unwrap();
                node_pos+=26;read+=1;
                if position&1==0 {(node_hash_v7(hash,c1,right1),node_hash_v7(hash,c2,right2))}
                else {(node_hash_v7(hash,right1,c1),node_hash_v7(hash,right2,c2))}
            };
            // Before this write: write < read, so no unread child is changed.
            level[write]=(position>>1,parent.0,parent.1);write+=1;
        }
        level.truncate(write);
    }
    node_pos==nodes.0.len() && level.len()==1 && level[0].0==0
        && level[0].1==*roots.0 && level[0].2==*roots.1
}
