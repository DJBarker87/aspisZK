-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_LPi_RawAssociation
set_option autoImplicit false
namespace AspisR1.LPi_RawValues
open Aeneas Aeneas.Std Result
abbrev Q := FIo_Native.fast_pairing.canonical.Q

def Canon (x : Q) : Prop :=
  x.val[0]!.val ≤ 2147483646 ∧ x.val[1]!.val ≤ 2147483646 ∧
  x.val[2]!.val ≤ 2147483646 ∧ x.val[3]!.val ≤ 2147483646

def spec (x y : Q) : Nat × Nat × Nat × Nat :=
  let a := x.val[0]!.val; let b := x.val[1]!.val
  let c := x.val[2]!.val; let d := x.val[3]!.val
  let e := y.val[0]!.val; let f := y.val[1]!.val
  let g := y.val[2]!.val; let h := y.val[3]!.val
  (R22RawQmProductResidues.rawC0 a b c d e f g h,
   R22RawQmProductResidues.rawC1 a b c d e f g h,
   R22RawQmProductResidues.rawC2 a b c d e f g h,
   R22RawQmProductResidues.rawC3 a b c d e f g h)

/-- Total concrete FIo raw call, with the existing repaired four-coordinate law.
No independently selected raw return or no-wrap hypothesis is supplied. -/
theorem source (x y : Q) (hx : Canon x) (hy : Canon y) : ∃ r0 r1 r2 r3 : U64,
    FIo_Native.fast_pairing.canonical.Q.raw x y = ok (Array.make 4#usize [r0,r1,r2,r3]) ∧
    (r0.val,r1.val,r2.val,r3.val) = spec x y := by
  obtain ⟨out,run⟩ := AspisR1S5QRawSourceTotality.qraw_total_of_canonical_limbs x y
    hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
  obtain ⟨a,b,c,d,e,f,g,h,r0,r1,r2,r3,shape,v0,v1,v2,v3,ea,eb,ec,ed,ee,ef,eg,eh⟩ :=
    AspisR1QRawActualC0V2.actual_raw_coefficients_of_input_bounds_v2 x y out run
      hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
  subst a; subst b; subst c; subst d; subst e; subst f; subst g; subst h
  refine ⟨r0,r1,r2,r3,?_,Prod.ext v0 (Prod.ext v1 (Prod.ext v2 v3))⟩
  rw [LPi_RawAssociation.source_eq,run,shape]

#print axioms source
end AspisR1.LPi_RawValues
