//! Research-only authentication order. Quotient/rho order is unchanged.
use super::*;
type Entry=(u32,V7Digest,V7Digest);
#[inline]
pub(super) fn entries(records:&[u8],queries:&[u32],hashfn:corelib::HashFn)->Result<Vec<Entry>,Error>{
    if queries.len()>Q{return Err(Error::Shape);}
    if records.len()<queries.len()*REC{return Err(Error::Length);}
    // Unique packed descriptors, including duplicate query ids. The low word
    // preserves the original ordinal. Only the populated prefix is sorted.
    let mut order=[0u64;Q];
    for(i,&key)in queries.iter().enumerate(){order[i]=(u64::from(key)<<32)|(i as u64);}
    order[..queries.len()].sort_unstable();
    let mut out=Vec::with_capacity(queries.len());
    for &descriptor in &order[..queries.len()]{
        let i=(descriptor as u32) as usize;let id=(descriptor>>32) as u32;
        let r=&records[i*REC..(i+1)*REC];let salt:&[u8;32]=r[589..621].try_into().unwrap();
        out.push((id,private_leaf_hash_v7(hashfn,V7_C1_TREE_TAG,&r[..403],salt),leaf_record::c2(hashfn,r)));
    }
    Ok(out)
}
#[cfg(test)]
mod tests {
    use super::*;
    fn reference(records:&[u8],queries:&[u32],h:corelib::HashFn)->Vec<Entry>{
        let mut out:Vec<_>=queries.iter().enumerate().map(|(i,&key)|{
            let r=&records[i*REC..(i+1)*REC];let salt=r[589..621].try_into().unwrap();
            (key,private_leaf_hash_v7(h,V7_C1_TREE_TAG,&r[..403],salt),private_leaf_hash_v7(h,V7_C2_TREE_TAG,&r[403..589],salt))
        }).collect();out.sort_by_key(|e|e.0);out
    }
    fn records()->Vec<u8>{(0..Q*REC).map(|i|((i*73+i/REC*19)%256) as u8).collect()}
    fn check(r:&[u8],q:&[u32]){assert_eq!(entries(r,q,hash).unwrap(),reference(r,q,hash));}
    #[test]
    fn all_small_orders_duplicates_and_large_keys(){
        let r=records();
        fn perms(r:&[u8],q:&mut[u32],n:usize){
            if n==q.len(){check(r,q);return;}
            for i in n..q.len(){q.swap(i,n);perms(r,q,n+1);q.swap(i,n);}
        }
        perms(&r,&mut[0,1,2,3,4,5],0);
        for n in 0..729u32{
            let mut t=n;let q:[u32;6]=core::array::from_fn(|_|{let k=t%3;t/=3;k});check(&r,&q);
            let e=entries(&r,&q,hash).unwrap();
            assert!(!verify_two_minimal_subtrees_v7_bytes(hash,(&[0;26],&[0;26]),18,&e,(&[],&[]),&mut vec![],&mut vec![]));
        }
        for n in 0..=Q{
            let q:Vec<u32>=(0..n).map(|i|if i%3==0{u32::MAX}else{(n-i) as u32}).collect();check(&r,&q);
            if n>0{assert_eq!(entries(&r[..n*REC-1],&q,hash),Err(Error::Length));}
        }
        assert_eq!(entries(&r,&[0;Q+1],hash),Err(Error::Shape));
        let mut rng=0x6f72_6465_725f_7638u64;
        for _ in 0..1024{
            let q:[u32;Q]=core::array::from_fn(|_|{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;rng as u32});check(&r,&q);
        }
    }
    #[test]
    fn stateful_hash_is_not_a_permitted_equivalence_backend(){
        std::thread_local!{static COUNT:std::cell::Cell<u8>=const{std::cell::Cell::new(0)};}
        fn stateful(_parts:&[&[u8]])->[u8;32]{COUNT.with(|c|{let v=c.get()+1;c.set(v);[v;32]})}
        let r=records();let q=[2,0,1];
        COUNT.with(|c|c.set(0));let old=reference(&r,&q,stateful);
        COUNT.with(|c|c.set(0));let new=entries(&r,&q,stateful).unwrap();
        assert_ne!(old,new);
    }
}
