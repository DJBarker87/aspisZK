use aspis_core::field::{QM31,CM31,M31};
pub(crate) fn q()->QM31 { let x:[u32;4]=kani::any(); QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}} }
pub(crate) fn qs<const N:usize>()->[QM31;N] { let mut a=[QM31::ZERO;N];let mut i=0;while i<N {a[i]=q();i+=1;}a }
