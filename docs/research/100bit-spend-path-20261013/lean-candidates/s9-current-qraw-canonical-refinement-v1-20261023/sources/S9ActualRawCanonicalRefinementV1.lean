import S9ActualRawKernelCouplingV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualRawCanonicalRefinementV1
open AspisR1S9ActualRawKernelsV1 AspisR1S9ActualRawKernelCouplingV1

/-- Auxiliary one-way execution transport: the actual release kernel follows
the SAME successful checked computation. Its success premise is discharged by
the public canonical-domain theorem below. No arbitrary-invalid-carrier
source/model equivalence is inferred. -/
theorem checked_raw_success_actual (left right : A4) (out : R4)
    (h : AspisR1CanonicalQRawUnified.canonical.Q.raw left right = .ok out) :
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw left right = .ok out := by
  obtain ⟨a,b,c,d,hl⟩ := List.length_eq_four.mp left.property
  obtain ⟨e,f,g,hh,hr⟩ := List.length_eq_four.mp right.property
  have hl' : left=Array.make 4#usize [a,b,c,d] := Subtype.ext hl
  have hr' : right=Array.make 4#usize [e,f,g,hh] := Subtype.ext hr
  subst left
  subst right
  rw [checked_raw_literal_prefix] at h
  rw [actual_raw_literal_prefix]
  exact checked_kernel_success_actual _ _ _ _ _ _ _ _ out h

/-- Actual unmodified H5 C Rust raw body refines the retained mathematical
kernel on the canonical operand domain required at its real private caller.
All checked-operation successes are DERIVED from existing S5 canonical
source totality, not supplied as extra premises. Complete Result equality is
claimed only on this valid domain; invalid carriers are deliberately outside
this statement. No physical Std.Array.map refinement is assumed: the actual
source uses direct reads/casts, the retained input-map model is mathematical. -/
theorem actual_raw_eq_checked_of_canonical (left right : A4)
    (hl0 : left.val[0]!.val ≤ 2^31-2) (hl1 : left.val[1]!.val ≤ 2^31-2)
    (hl2 : left.val[2]!.val ≤ 2^31-2) (hl3 : left.val[3]!.val ≤ 2^31-2)
    (hr0 : right.val[0]!.val ≤ 2^31-2) (hr1 : right.val[1]!.val ≤ 2^31-2)
    (hr2 : right.val[2]!.val ≤ 2^31-2) (hr3 : right.val[3]!.val ≤ 2^31-2) :
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw left right =
      AspisR1CanonicalQRawUnified.canonical.Q.raw left right := by
  obtain ⟨out,hold⟩ := AspisR1S5QRawSourceTotality.qraw_total_of_canonical_limbs
    left right hl0 hl1 hl2 hl3 hr0 hr1 hr2 hr3
  have hactual := checked_raw_success_actual left right out hold
  exact hactual.trans hold.symm

theorem actual_raw_success_checked_of_canonical (left right : A4) (out : R4)
    (hl0 : left.val[0]!.val ≤ 2^31-2) (hl1 : left.val[1]!.val ≤ 2^31-2)
    (hl2 : left.val[2]!.val ≤ 2^31-2) (hl3 : left.val[3]!.val ≤ 2^31-2)
    (hr0 : right.val[0]!.val ≤ 2^31-2) (hr1 : right.val[1]!.val ≤ 2^31-2)
    (hr2 : right.val[2]!.val ≤ 2^31-2) (hr3 : right.val[3]!.val ≤ 2^31-2)
    (h : AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw left right = .ok out) :
    AspisR1CanonicalQRawUnified.canonical.Q.raw left right = .ok out := by
  rw [←actual_raw_eq_checked_of_canonical left right hl0 hl1 hl2 hl3 hr0 hr1 hr2 hr3]
  exact h

#print axioms checked_raw_success_actual
#print axioms actual_raw_eq_checked_of_canonical
#print axioms actual_raw_success_checked_of_canonical
end AspisR1S9ActualRawCanonicalRefinementV1
