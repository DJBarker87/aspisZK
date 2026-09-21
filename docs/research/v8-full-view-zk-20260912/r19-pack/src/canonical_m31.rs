//! Uncompiled canonical-only microbenchmark helpers, NOT a global overflow toggle.
//! All inputs must already be < P under the ACTUAL caller invariant.
//! Keep canonical byte validation and the general full-u64 reducer unchanged.
use super::corelib::field::M31;
const P:u32=0x7fff_ffff;
#[inline(always)]pub fn add(a:M31,b:M31)->M31{
    debug_assert!(a.0<P&&b.0<P);let s=a.0.wrapping_add(b.0);M31(if s>=P{s-P}else{s})
}
#[inline(always)]pub fn sub(a:M31,b:M31)->M31{
    debug_assert!(a.0<P&&b.0<P);let s=a.0.wrapping_add(P).wrapping_sub(b.0);M31(if s>=P{s-P}else{s})
}
#[inline(always)]pub fn mul(a:M31,b:M31)->M31{
    debug_assert!(a.0<P&&b.0<P);
    let p=(a.0 as u64).wrapping_mul(b.0 as u64);
    let s=(p&(P as u64)).wrapping_add(p>>31) as u32;
    M31(if s>=P{s-P}else{s})
}
#[inline(always)]pub fn halves<const N:u32>(a:M31)->M31{
    assert!(N<=30);debug_assert!(a.0<P);
    if N==0{a}else{M31((a.0>>N)|((a.0&((1u32<<N)-1))<<(31-N)))}
}
