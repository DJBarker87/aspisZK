//! Actual staged caller differential: arbitrary authenticated records, not
//! honest witness encodings. Hashes and verifiers are the real source ones.
use super::*;
use std::collections::{BTreeMap,BTreeSet};
fn word(r:&mut u64)->u32{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;(*r%u64::from(corelib::field::P)) as u32}
fn k(r:&mut u64)->K{K{c0:CM31::new(M31(word(r)),M31(word(r))),c1:CM31::new(M31(word(r)),M31(word(r)))}}
fn set_limb(b:&mut[u8],i:usize,x:u32){for bit in 0..31 {let at=31*i+bit;let mask=1u8<<(at%8);b[at/8]=(b[at/8]&!mask)|((((x>>bit)&1) as u8)<<(at%8));}}
fn tree(records:&[u8],ids:&[u32],channel:usize)->([u8;26],Vec<u8>){
    let mut nodes:BTreeMap<u32,[u8;26]>=ids.iter().enumerate().map(|(i,&id)|{
        let r=&records[i*REC..(i+1)*REC];let salt=r[589..621].try_into().unwrap();
        let leaf=if channel==0 {private_leaf_hash_v7(hash,V7_C1_TREE_TAG,&r[..403],salt)}
            else {private_leaf_hash_v7(hash,V7_C2_TREE_TAG,&r[403..589],salt)};
        (id,leaf)
    }).collect();
    let mut frontier=vec![];
    for level in 0u32..18 {
        let mut full=nodes.clone();
        for &id in nodes.keys(){if !nodes.contains_key(&(id^1)){
            let digest=hash(&[b"R19/arbitrary-authenticated-subtree",&level.to_le_bytes(),&(id^1).to_le_bytes(),&[channel as u8]]);
            let sibling:[u8;26]=digest[..26].try_into().unwrap();frontier.extend_from_slice(&sibling);full.insert(id^1,sibling);
        }}
        let parents:BTreeSet<u32>=nodes.keys().map(|id|id>>1).collect();
        nodes=parents.into_iter().map(|id|(id,node_hash_v7(hash,&full[&(2*id)],&full[&(2*id+1)]))).collect();
    }
    (nodes[&0],frontier)
}
fn wire<'a>(records:&'a[u8],roots:([u8;26],[u8;26]),front:(&'a[u8],&'a[u8]))->Wire<'a>{
    Wire{v:vec![K::ZERO;FIXED],roots,nonces:&[0;24],records,frontiers:front}
}
fn compare(w:&Wire<'_>,p:&Prefix,g:[K;2],ids:&[u32],a:K)->Result<([Vec<K>;2],Vec<M31>),Error>{
    let primary=r17_relation::opened_mode(w,p,g,ids,a,false);
    let with_reference=r17_relation::opened_mode(w,p,g,ids,a,true);
    assert_eq!(primary,with_reference,"primary versus retained actual wrapper");
    // On rejection the original wrapper never reaches its extra reference;
    // compare errors to THAT wrapper, not a differently ordered standalone.
    if let Ok((values,xs))=&primary {
        let old=Prefix{t:p.t.clone(),points:p.points,gamma:p.gamma,abc:p.abc,
            iv:[p.iv[0].add(g[0]),p.iv[1].add(g[1])],use_x:p.use_x,tau:p.tau};
        let (v,y)=opened_values_reference(w,&old,ids,a,hash).unwrap();
        assert_eq!(&y,xs);assert_eq!(v,values[0].iter().zip(&values[1]).map(|(r,g)|r.add(*g)).collect::<Vec<_>>());
    }
    primary
}
pub(super) fn run(){
    let mut rng=0x193721692026u64;
    let ids:Vec<u32>=(0..Q).map(|i|((i*11719+7919)%262144) as u32).collect();
    let points=corelib::circle_fri::selected_circle_fiber_points_shared(20,&ids).unwrap();
    let dummy=Point{x:K::ONE,y:K::ZERO};
    let mut records=vec![0u8;Q*REC];
    for case in 0..32 {
        for i in 0..Q {let r=&mut records[i*REC..(i+1)*REC];
            for j in 0..104 {set_limb(&mut r[..403],j,word(&mut rng));}
            for j in 0..48 {set_limb(&mut r[403..589],j,word(&mut rng));}
            for b in &mut r[589..] {*b=word(&mut rng) as u8;}
        }
        let (ra,fa)=tree(&records,&ids,0);let (rb,fb)=tree(&records,&ids,1);
        let w=wire(&records,(ra,rb),(&fa,&fb));
        let mut p=Prefix{t:Transcript::new(hash),points:[dummy;2],gamma:k(&mut rng),
            abc:core::array::from_fn(|_|k(&mut rng)),iv:[k(&mut rng),k(&mut rng)],use_x:case%2==0,tau:k(&mut rng)};
        let g=[k(&mut rng),k(&mut rng)];let a=match case {0=>K::ZERO,1=>K::ONE,_=>k(&mut rng)};
        assert!(compare(&w,&p,g,&ids,a).is_ok());
        if case!=0 {continue;}
        // Every packed limb in every actual record, including separately read G.
        for i in 0..Q {for j in 0..152 {
            let mut bad=records.clone();let r=&mut bad[i*REC..(i+1)*REC];
            if j<104 {set_limb(&mut r[..403],j,corelib::field::P)}else{set_limb(&mut r[403..589],j-104,corelib::field::P)}
            assert_eq!(compare(&wire(&bad,(ra,rb),(&fa,&fb)),&p,g,&ids,a),Err(Error::Canonical));
        }}
        for i in 0..Q {for at in [0,403,589,620] {
            let mut bad=records.clone();bad[i*REC+at]^=1;
            assert!(compare(&wire(&bad,(ra,rb),(&fa,&fb)),&p,g,&ids,a).is_err());
        }}
        // Every frontier node in both roots, and all 52 root bytes.
        for channel in 0..2 {let f=if channel==0 {&fa}else{&fb};for at in (0..f.len()).step_by(26){
            let mut bad=f.clone();bad[at]^=1;
            let fronts=if channel==0{(bad.as_slice(),fb.as_slice())}else{(fa.as_slice(),bad.as_slice())};
            assert_eq!(compare(&wire(&records,(ra,rb),fronts),&p,g,&ids,a),Err(Error::Authentication));
        }}
        for at in 0..52 {let(mut x,mut y)=(ra,rb);if at<26{x[at]^=1}else{y[at-26]^=1};
            assert_eq!(compare(&wire(&records,(x,y),(&fa,&fb)),&p,g,&ids,a),Err(Error::Authentication));}
        for i in 0..Q {let mut bad=ids.clone();bad[i]^=1;
            assert!(compare(&w,&p,g,&bad,a).is_err());}
        let abc=p.abc;
        for base in &points {for(x,y)in [(base.x,base.y),(base.x,base.y.neg()),(base.x.neg(),base.y.neg()),(base.x.neg(),base.y)] {
            p.abc=[abc[1].mul_m31(x).add(abc[2].mul_m31(y)).neg(),abc[1],abc[2]];
            assert_eq!(compare(&w,&p,g,&ids,a),Err(Error::Domain));
        }}
        p.abc=abc;
        // Combined faults ensure the original wrapper's per-record error order.
        let mut bad=records.clone();set_limb(&mut bad[..403],0,corelib::field::P);
        p.abc=[K::ZERO;3];
        assert_eq!(compare(&wire(&bad,(ra,rb),(&fa,&fb)),&p,g,&ids,a),Err(Error::Canonical));
        let mut bad=records.clone();set_limb(&mut bad[REC..REC+403],0,corelib::field::P);
        assert_eq!(compare(&wire(&bad,(ra,rb),(&fa,&fb)),&p,g,&ids,a),Err(Error::Domain));
    }
    println!("R19_OPENING source_arbitrary_authenticated=32 canonical_positions=3344 chord_poles=88 roots=52 record_mutations=88 query_indices=22 frontier_nodes=all wrapper_error_order=true reference_retained=true");
}
