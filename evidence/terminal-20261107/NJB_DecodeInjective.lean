import NJB_Words
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_DecodeInjective
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
abbrev M := AspisV8R15.ExactTowerBase.M31Exact
/-- Canonical scalar casts are injective; no large concrete numeral is reduced. -/
theorem word (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647)
 (same : (x.val : M)=(y.val : M)) : x=y := by
 apply UScalar.eq_of_val_eq
 have values := congrArg ZMod.val same
 simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using values
/-- Exact raw four-word carrier equality follows from equality of the retained
quadratic-tower value only when BOTH records are canonical. -/
theorem qm (x y : NQ) (hx : Canon x) (hy : Canon y) (same : decode x=decode y) : x=y := by
 change (⟨⟨(x.c0.a.val : M),(x.c0.b.val : M)⟩,⟨(x.c1.a.val : M),(x.c1.b.val : M)⟩⟩ : K)=
  (⟨⟨(y.c0.a.val : M),(y.c0.b.val : M)⟩,⟨(y.c1.a.val : M),(y.c1.b.val : M)⟩⟩ : K) at same
 injection same with h0 h1
 injection h0 with ha hb
 injection h1 with hc hd
 apply NJB_Words.ext x y
 intro i
 fin_cases i
 · exact word x.c0.a y.c0.a hx.1.1 hy.1.1 ha
 · exact word x.c0.b y.c0.b hx.1.2 hy.1.2 hb
 · exact word x.c1.a y.c1.a hx.2.1 hy.2.1 hc
 · exact word x.c1.b y.c1.b hx.2.2 hy.2.2 hd
theorem list (xs ys : List NQ) (hx : ∀ x∈xs,Canon x) (hy : ∀ y∈ys,Canon y)
 (same : xs.map decode=ys.map decode) : xs=ys := by
 induction xs generalizing ys with
 | nil => cases ys with | nil => rfl | cons y ys => cases same
 | cons x xs ih =>
   cases ys with
   | nil => cases same
   | cons y ys =>
     have cells := List.cons.inj same
     have first := qm x y (hx x (by simp)) (hy y (by simp)) cells.1
     have tail := ih ys (fun z hz=>hx z (by simp [hz])) (fun z hz=>hy z (by simp [hz])) cells.2
     exact congrArg₂ List.cons first tail
theorem array {N : Usize} (xs ys : Array NQ N) (hx : FIw_ArrayValue.canonical xs)
 (hy : FIw_ArrayValue.canonical ys) (same : xs.val.map decode=ys.val.map decode) : xs=ys :=
 Subtype.ext (list xs.val ys.val hx hy same)
#print axioms word
#print axioms qm
#print axioms list
#print axioms array
end AspisR1.NJB_DecodeInjective
end
