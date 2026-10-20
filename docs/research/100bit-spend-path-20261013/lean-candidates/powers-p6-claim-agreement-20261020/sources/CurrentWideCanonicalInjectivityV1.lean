import CurrentPowersExactProduct
import ExtractedCurrentQM31Equality
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWideCanonicalInjectivityV1
open AspisR1CurrentWide AspisR1CurrentWide.Proof

def fromCurrentQM (x : AspisR1.ExtractedCurrentQM31Exact.CurrentQM) : field.QM31 :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩

theorem from_to_currentQM (x : field.QM31) : fromCurrentQM (toQM x)=x := rfl

theorem canonical_wide_decode_eq_iff (x y : E)
    (hx : CanonicalWide x) (hy : CanonicalWide y) :
    decodeWide x=decodeWide y ↔ x=y := by
  constructor
  · intro h
    have h0 : decodeQM x.c0=decodeQM y.c0 :=
      congrArg (fun z : AspisWideTower.WideExact => z.re) h
    have h1 : decodeQM x.c1=decodeQM y.c1 :=
      congrArg (fun z : AspisWideTower.WideExact => z.im) h
    have e0 := (AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff
      (toQM x.c0) (toQM y.c0) hx.1 hy.1).mp h0
    have e1 := (AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff
      (toQM x.c1) (toQM y.c1) hx.2 hy.2).mp h1
    have c0 : x.c0=y.c0 := congrArg fromCurrentQM e0
    have c1 : x.c1=y.c1 := congrArg fromCurrentQM e1
    cases x with
    | mk x0 x1 =>
      cases y with
      | mk y0 y1 =>
        cases c0
        cases c1
        rfl
  · intro h
    cases h
    rfl

theorem canonical_callback_decode_eq_iff
    (x y : AspisR1PowersConcreteMul.CallbackWide)
    (hx : AspisR1PowersConcreteMul.Canonical x) (hy : AspisR1PowersConcreteMul.Canonical y) :
    AspisR1PowersExactProduct.decode x=AspisR1PowersExactProduct.decode y ↔ x=y := by
  constructor
  · intro h
    have he := (canonical_wide_decode_eq_iff
      (AspisR1PowersExactProduct.toFull x) (AspisR1PowersExactProduct.toFull y) hx hy).mp h
    exact congrArg AspisR1PowersExactProduct.fromFull he
  · intro h
    cases h
    rfl

#print axioms from_to_currentQM
#print axioms canonical_wide_decode_eq_iff
#print axioms canonical_callback_decode_eq_iff
end AspisR1CurrentWideCanonicalInjectivityV1
