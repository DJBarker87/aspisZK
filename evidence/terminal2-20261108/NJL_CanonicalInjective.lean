import NJB_Words
set_option autoImplicit false
namespace AspisR1.NJL_CanonicalInjective
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open ExtractedMaskQM31Exact (M31Exact)
theorem word (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647)
 (same : (x.val : M31Exact)=(y.val : M31Exact)) : x=y := by
 apply UScalar.eq_of_val_eq
 have value := congrArg ZMod.val same
 simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using value
/-- Canonical native carriers are uniquely determined by retained exact-field
decoding; this closes native/reference/adopted returned-array identity. -/
theorem qm (x y : NQ) (hx : Canon x) (hy : Canon y) (same : decode x=decode y) : x=y := by
 apply NJB_Words.ext
 intro i
 fin_cases i
 · exact word _ _ hx.1.1 hy.1.1 (congrArg (fun q=>q.re.re) same)
 · exact word _ _ hx.1.2 hy.1.2 (congrArg (fun q=>q.re.im) same)
 · exact word _ _ hx.2.1 hy.2.1 (congrArg (fun q=>q.im.re) same)
 · exact word _ _ hx.2.2 hy.2.2 (congrArg (fun q=>q.im.im) same)
#print axioms word
#print qm
#print axioms qm
end AspisR1.NJL_CanonicalInjective
