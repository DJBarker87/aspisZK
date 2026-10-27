use super::*;
#[kani::proof] #[kani::unwind(6)]
fn LPa_dot_stage() {
    let x:[u32;4]=kani::any(); let y:[u32;4]=kani::any();
    kani::assume(x.iter().all(|v|*v<P)); kani::assume(y.iter().all(|v|*v<P));
    let a=Q::from_limbs(x).unwrap(); let b=Q::from_limbs(y).unwrap();
    let sums:[u64;4]=kani::any(); let mut actual=Dot{sums};
    let raw=a.raw(b); actual.push(a,b);
    let j:usize=kani::any();kani::assume(j<4);
    let expected=sums[j].wrapping_add((raw[j]%(1u64<<31)).wrapping_add(raw[j]/(1u64<<31)));
    assert_eq!(actual.sums[j],expected);
}
