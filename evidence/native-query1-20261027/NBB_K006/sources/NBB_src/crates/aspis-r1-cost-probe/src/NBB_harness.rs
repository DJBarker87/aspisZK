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

fn NBB_add(old:u64,limb:u32,basis:M31)->u64 {old+u64::from(limb)*u64::from(basis.0)}
static mut NBB_RAW:u64=0;
static mut NBB_LIMB:u32=0;
static mut NBB_REPLY:u64=0;
fn NBB_add_reply(old:u64,limb:u32,basis:M31)->u64 {
    unsafe {NBB_RAW=old;NBB_LIMB=limb;NBB_BASIS=basis.0;let out=kani::any();NBB_REPLY=out;out}
}
// Literal one-iteration body, factoring only the checked integer scalar leaf.
fn NBB_add_iteration(row:&mut[u64;4],limbs:&[u32;4],basis:M31,j:usize) {
    let old=residue_limb_at(row,j);
    let limb=power_limb_at(limbs,j);
    row[j]=NBB_add(old,limb,basis);
}
#[kani::proof]
#[kani::stub(NBB_add,NBB_add_reply)]
fn NBB_add_frame() {
    let mut row:[u64;4]=kani::any();let limbs:[u32;4]=kani::any();
    let j:usize=kani::any();kani::assume(j<4);
    let k:usize=kani::any();kani::assume(k<4);
    let basis:u32=kani::any();let old=row[j];let before=row[k];
    NBB_add_iteration(&mut row,&limbs,M31(basis),j);
    unsafe {assert_eq!(NBB_RAW,old);assert_eq!(NBB_LIMB,limbs[j]);assert_eq!(NBB_BASIS,basis);
        assert_eq!(row[k],if k==j {NBB_REPLY} else {before});}
    kani::cover!(j==0);kani::cover!(j==3);kani::cover!(j!=k);
}
fn NBB_fold(value:u64)->u64 {(value&0x7fff_ffff)+(value>>31)}
fn NBB_fold_reply(value:u64)->u64 {
    unsafe {NBB_RAW=value;let out=kani::any();NBB_REPLY=out;out}
}
#[kani::proof]
#[kani::unwind(5)]
#[kani::stub(NBB_fold,NBB_fold_reply)]
fn NBB_fold_frame() {
    let mut row:[u64;4]=kani::any();let before=row;
    let j:usize=kani::any();kani::assume(j<4);
    let k:usize=kani::any();kani::assume(k<4);
    let mut it=row.iter_mut();
    for _ in 0..j {let _=it.next().unwrap();}
    let limb=it.next().unwrap();*limb=NBB_fold(*limb);
    unsafe {assert_eq!(NBB_RAW,before[j]);assert_eq!(row[k],if j==k {NBB_REPLY} else {before[k]});}
    kani::cover!(j==0);kani::cover!(j==3);kani::cover!(j!=k);
}

// The native continuation after Vec's checked indexed borrow. The Vec borrow
// itself uses the retained standard-library interpretation; no64-row loop runs.
fn NBB_push_selected(row:&mut[u64;4],terms:usize,power:K,basis:M31) {
    let flush=terms&3==3;
    update_residue_row(row,power,basis,flush);
}
#[kani::proof]
#[kani::stub(super::update_residue_row,NBB_row_reply)]
fn NBB_push_selected_frame() {
    let mut row:[u64;4]=kani::any();let before=row;
    let p:[u32;4]=kani::any();let basis:u32=kani::any();let terms:usize=kani::any();
    let limb:usize=kani::any();kani::assume(limb<4);
    let power=K{c0:CM31{a:M31(p[0]),b:M31(p[1])},c1:CM31{a:M31(p[2]),b:M31(p[3])}};
    NBB_push_selected(&mut row,terms,power,M31(basis));
    unsafe {
        assert_eq!(NBB_CALLS,1);assert_eq!(NBB_OLD[limb],before[limb]);
        assert_eq!(NBB_POWER[limb],p[limb]);assert_eq!(NBB_BASIS,basis);
        assert_eq!(NBB_FLUSH,terms&3==3);assert_eq!(row[limb],NBB_OUT[limb]);
    }
    kani::cover!(terms&3==3);kani::cover!(terms&3!=3);
}

// Changed initialization cut after K001: one owned array allocation, no Vec append loop.
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(super::update_residue_row,NBB_row_reply)]
fn NBB_push_array_frame() {
    let raw=Vec::from([
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>(),
        kani::any::<[u64;4]>()
    ]);
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

#[kani::proof]
fn NBB_range_step() {
 let j:usize=kani::any();kani::assume(j<=4);
 let mut iter=j..4;let out=iter.next();
 if j<4 {assert_eq!(out,Some(j));assert_eq!(iter.start,j+1);}
 else {assert!(out.is_none());assert_eq!(iter.start,j);}
 assert_eq!(iter.end,4);
 kani::cover!(j==0);kani::cover!(j==3);kani::cover!(j==4);
}
