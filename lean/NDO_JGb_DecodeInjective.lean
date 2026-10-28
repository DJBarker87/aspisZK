import NDO_JGb_Terminal
set_option autoImplicit false
namespace AspisR1.JGb_DecodeInjective
open Aeneas Aeneas.Std FIq_Native
open FIv_NativeValue (Canon decode)

theorem word (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647)
    (same : (x.val : ZMod 2147483647)=(y.val : ZMod 2147483647)) : x=y := by
  apply UScalar.val_eq_imp x y
  have h := congrArg ZMod.val same
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using h
#print axioms word

theorem source (x y : field.QM31) (hx : Canon x) (hy : Canon y) (same : decode x=decode y) : x=y := by
  have e00 := word x.c0.a y.c0.a hx.1.1 hy.1.1 (congrArg (fun q => q.re.re) same)
  have e01 := word x.c0.b y.c0.b hx.1.2 hy.1.2 (congrArg (fun q => q.re.im) same)
  have e10 := word x.c1.a y.c1.a hx.2.1 hy.2.1 (congrArg (fun q => q.im.re) same)
  have e11 := word x.c1.b y.c1.b hx.2.2 hy.2.2 (congrArg (fun q => q.im.im) same)
  cases x with | mk x0 x1 =>
    cases x0;cases x1
    cases y with | mk y0 y1 =>
      cases y0;cases y1
      simp_all
#print axioms source
end AspisR1.JGb_DecodeInjective
