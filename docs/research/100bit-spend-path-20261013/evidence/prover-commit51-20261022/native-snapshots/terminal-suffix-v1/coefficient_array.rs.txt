mod coefficient_array_gate {
type K=[u32;4];
pub(super) fn row(j:usize)->usize{let tau=[3,4,2,0,1];let mut out=0;for d in 0..5{out|=((j>>(2*d))&3)<<(2*tau[d]);}out}
fn coefficients(rows:&[K;1024])->[K;1024]{core::array::from_fn(|j|rows[row(j)])}
pub(super) fn owned_row(j:usize)->usize{(j/64)%4+4*((j/256)%4)+16*((j/16)%4)+64*(j%4)+256*((j/4)%4)}
#[cfg(kani)]mod proofs{use super::*;
#[kani::proof]#[kani::unwind(1027)]fn coefficient_array(){let rows:[K;1024]=kani::any();let j:usize=kani::any();kani::assume(j<1024);let out=coefficients(&rows);let r=owned_row(j);for k in 0..4{assert_eq!(out[j][k],rows[r][k]);}}
}
}

#[cfg(kani)]mod callback_proofs{
#[kani::proof]#[kani::unwind(7)]fn callback(){let j:usize=kani::any();kani::assume(j<1024);let n=super::coefficient_array_gate::row(j);let o=super::coefficient_array_gate::owned_row(j);assert_eq!(n,o);assert!(n<1024);}
}
