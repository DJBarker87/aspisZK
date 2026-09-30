extern crate alloc;
extern crate aspis_core as corelib;
pub use corelib::{field,circle,sumcheck};
#[path="r98_reference_transcript.rs"]mod reference;
use sha2::{Digest,Sha256};
std::thread_local!{static TRACE:std::cell::RefCell<Vec<Vec<Vec<u8>>>>=const{std::cell::RefCell::new(Vec::new())};}
fn hash(parts:&[&[u8]])->[u8;32]{
    TRACE.with(|t|t.borrow_mut().push(parts.iter().map(|p|p.to_vec()).collect()));
    let mut h=Sha256::new();for p in parts{h.update(p);}h.finalize().into()
}
fn zero(parts:&[&[u8]])->[u8;32]{let _=hash(parts);[0;32]}
fn stateful(parts:&[&[u8]])->[u8;32]{let _=hash(parts);let n=TRACE.with(|t|t.borrow().len())as u32;
    let mut out=[0;32];for i in 0..8{out[4*i..4*i+4].copy_from_slice(&(n*4+i as u32/2).to_le_bytes());}out}
fn main(){
    let mut count=0;let mut seed=0x98a001cc24310908u64;
    for i in 0..1000000u32{
        let b=if i<65536{i}else{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;seed as u32};
        assert_eq!(b!=0&&(b&(b-1))==0,b.is_power_of_two());
    }
    for n in 0..32{for b in [(1u32<<n)-1,1u32<<n,(1u32<<n).saturating_add(1)]{
        assert_eq!(b!=0&&(b&(b-1))==0,b.is_power_of_two());}}
    for hash in [hash as corelib::HashFn,zero,stateful]{for prefix in 0..4u8{
        for b in [0,1,2,3,4,31,32,33,1<<18,1<<31,u32::MAX]{for c in [0,1,2,22,65,255]{
            for cap in [0,1,7,8,9,23,63,64,65]{
                TRACE.with(|t|t.borrow_mut().clear());
                let mut old=reference::Transcript::new(hash);old.absorb(1,&[prefix;32]);
                let a=format!("{:?}",old.challenge_queries_without_replacement(c,b,cap));
                let after_a=old.squeeze_block();
                let trace=TRACE.with(|t|core::mem::take(&mut *t.borrow_mut()));
                let mut new=corelib::transcript::Transcript::new(hash);new.absorb(1,&[prefix;32]);
                let b=format!("{:?}",new.challenge_queries_without_replacement(c,b,cap));
                let after_b=new.squeeze_block();
                let new_trace=TRACE.with(|t|core::mem::take(&mut *t.borrow_mut()));
                assert_eq!(a,b);assert_eq!(after_a,after_b);assert_eq!(trace,new_trace);count+=1;
            }
        }}
    }}
    assert_eq!(corelib::transcript::transcript_kat(hash),reference::TRANSCRIPT_KAT_EXPECTED);
    println!("R98_QUERY public_calls={count} guard_cases=1000096 ordered_hash_calls_equal=true stateful_backend_equal=true kat_pinned=true");
}
