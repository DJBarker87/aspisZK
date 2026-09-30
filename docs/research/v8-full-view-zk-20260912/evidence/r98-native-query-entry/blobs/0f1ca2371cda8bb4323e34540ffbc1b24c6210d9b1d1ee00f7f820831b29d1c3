extern crate aspis_core as corelib;
use corelib::v7_merkle208::*;
use sha2::{Digest,Sha256};
mod r95_merkle;
type Entry=(u32,V7Digest,V7Digest);
std::thread_local!{static TRACE:std::cell::RefCell<Vec<Vec<Vec<u8>>>>=const{std::cell::RefCell::new(Vec::new())};}
fn hash(parts:&[&[u8]])->[u8;32]{
    TRACE.with(|t|t.borrow_mut().push(parts.iter().map(|p|p.to_vec()).collect()));
    let mut h=Sha256::new();for p in parts{h.update(p);}h.finalize().into()
}
fn stateful(parts:&[&[u8]])->[u8;32]{
    let h=hash(parts);let n=TRACE.with(|t|t.borrow().len());
    core::array::from_fn(|i|h[i]^(n as u64).rotate_left(i as u32)as u8)
}
fn compare(hash:corelib::HashFn,roots:(&V7Digest,&V7Digest),depth:u32,e:&[Entry],a:&[u8],b:&[u8])->bool{
    TRACE.with(|t|t.borrow_mut().clear());
    let old=verify_two_minimal_subtrees_v7_bytes(hash,roots,depth,e,(a,b),&mut vec![],&mut vec![]);
    let trace=TRACE.with(|t|core::mem::take(&mut *t.borrow_mut()));
    let new=r95_merkle::verify(hash,roots,depth,e,(a,b));
    let new_trace=TRACE.with(|t|core::mem::take(&mut *t.borrow_mut()));
    assert_eq!(new,old);assert_eq!(new_trace,trace);new
}
fn main(){
    let mut cases=0;let mut honest=0;let mut seed=0x7269_6768_742d_7265u64;
    for depth in 0..=8u32 {
        let n=1usize<<depth;
        let leaves:Vec<Entry>=(0..n).map(|i|(i as u32,core::array::from_fn(|j|(i*73+j*31)as u8),
            core::array::from_fn(|j|(i*43+j*67+11)as u8))).collect();
        let mut layers=vec![leaves];
        for _ in 0..depth {
            let next=layers.last().unwrap().chunks_exact(2).map(|c|
                (c[0].0>>1,node_hash_v7(hash,&c[0].1,&c[1].1),node_hash_v7(hash,&c[0].2,&c[1].2))).collect();
            layers.push(next);
        }
        let schedules=if depth<=3{(1usize<<n)-1}else{64};
        for schedule in 1..=schedules {
            let mut ids:Vec<u32>=(0..n).filter(|&i|if depth<=3 {schedule&(1usize<<i)!=0}else{
                seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;seed%11==0
            }).map(|i|i as u32).collect();
            if ids.is_empty(){ids.push((schedule%n)as u32);}
            let entries:Vec<Entry>=ids.iter().map(|&i|layers[0][i as usize]).collect();
            let(mut a,mut b)=(vec![],vec![]);
            for layer in &layers[..depth as usize]{
                for &i in &ids{if ids.binary_search(&(i^1)).is_err(){a.extend(layer[(i^1)as usize].1);b.extend(layer[(i^1)as usize].2);}}
                for i in &mut ids{*i>>=1;}ids.dedup();
            }
            let root=layers[depth as usize][0];let roots=(&root.1,&root.2);
            assert!(compare(hash,roots,depth,&entries,&a,&b));honest+=1;cases+=1;
            let mut check=|d,e:&[Entry],aa:&[u8],bb:&[u8]|{assert!(!compare(hash,roots,d,e,aa,bb));cases+=1;};
            check(depth,&[],&a,&b);check(32,&entries,&a,&b);
            let mut duplicate=entries.clone();duplicate.insert(0,duplicate[0]);check(depth,&duplicate,&a,&b);
            let mut bad=entries.clone();bad[0].1[0]^=1;check(depth,&bad,&a,&b);
            bad=entries.clone();bad[0].2[25]^=1;check(depth,&bad,&a,&b);
            bad=entries.clone();bad.last_mut().unwrap().0=1u32<<depth;check(depth,&bad,&a,&b);
            if entries.len()>1 {bad=entries.clone();bad.reverse();check(depth,&bad,&a,&b);}
            if !a.is_empty(){check(depth,&entries,&a[..a.len()-1],&b);check(depth,&entries,&a[..a.len()-26],&b[..b.len()-26]);
                let mut aa=a.clone();aa[0]^=1;check(depth,&entries,&aa,&b);
                let mut bb=b.clone();let last=bb.len()-1;bb[last]^=1;check(depth,&entries,&a,&bb);}
            let mut aa=a.clone();let mut bb=b.clone();aa.extend([0;26]);bb.extend([0;26]);
            check(depth,&entries,&aa,&bb);
            // No purity assumption: even a stateful backend sees the same calls.
            compare(stateful,roots,depth,&entries,&a,&b);cases+=1;
        }
    }
    println!("R95_MERKLE honest_schedules={honest} cases={cases} ordered_segmented_hash_calls_equal=true stateful_backend_equal=true");
}
