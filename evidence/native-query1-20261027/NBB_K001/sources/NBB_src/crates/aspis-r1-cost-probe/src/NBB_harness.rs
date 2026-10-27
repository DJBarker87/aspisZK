use super::*;
use aspis_core::field::CM31;
static mut NBB_OLD:[u64;4]=[0;4];
static mut NBB_OUT:[u64;4]=[0;4];
static mut NBB_POWER:[u32;4]=[0;4];
static mut NBB_BASIS:u32=0;
static mut NBB_FLUSH:bool=false;
static mut NBB_CALLS:usize=0;

// Overapproximation of the row leaf; NBB_Row.source proves totality and the
// unique actual value on the caller's phase/canonical domain. No multiply runs.
fn NBB_row_reply(row:&mut[u64;4],power:K,basis:M31,flush:bool) {
    unsafe {
        NBB_OLD=*row;
        NBB_POWER=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
        NBB_BASIS=basis.0;NBB_FLUSH=flush;NBB_CALLS+=1;
        let out:[u64;4]=kani::any();NBB_OUT=out;*row=out;
    }
}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(super::update_residue_row,NBB_row_reply)]
fn NBB_push_frame() {
    let mut raw=Vec::with_capacity(64);
    for _ in 0..64 {raw.push(kani::any::<[u64;4]>());}
    let terms:usize=kani::any();
    let index:usize=kani::any();kani::assume(index<64);
    let selected:usize=kani::any();kani::assume(selected<64);
    let limb:usize=kani::any();kani::assume(limb<4);
    let before=raw[selected][limb];let old=raw[index][limb];
    let p:[u32;4]=kani::any();let basis:u32=kani::any();
    let power=K{c0:CM31{a:M31(p[0]),b:M31(p[1])},c1:CM31{a:M31(p[2]),b:M31(p[3])}};
    let mut weights=BatchedWeights{raw,terms};
    weights.push(index,power,M31(basis));
    assert_eq!(weights.terms,terms);assert_eq!(weights.raw.len(),64);
    unsafe {
        assert_eq!(NBB_CALLS,1);assert_eq!(NBB_OLD[limb],old);
        assert_eq!(NBB_POWER[limb],p[limb]);assert_eq!(NBB_BASIS,basis);
        assert_eq!(NBB_FLUSH,terms&3==3);
        assert_eq!(weights.raw[selected][limb],if selected==index {NBB_OUT[limb]} else {before});
    }
    kani::cover!(index==0);kani::cover!(index==63);
    kani::cover!(selected!=index);kani::cover!(terms&3==3);
}
