import R0P.Core
import R1ExactBaseProjection

/-! A computable bounded-value decoder for the three value cells in a wide
trace.  This only projects those cells into the exact M31 base and checks the
requested 30-bit bounds; it makes no claim that a protocol execution supplied
the trace or that production constraints hold. -/

set_option autoImplicit false

namespace AspisR1.TraceValueDecode

open R0P
open AspisV8R15.ExactTowerBase
open AspisWideTower

abbrev Values := Fin (2 ^ 30) × Fin (2 ^ 30) × Fin (2 ^ 30)

/-- Read the three value cells, project them to M31, and accept exactly
when all three canonical representatives fit in 30 bits. -/
def decode (A : Trace WideExact) : Option Values :=
  let v0 := (ExactBaseProjection.project (A 10 1008)).val
  let v1 := (ExactBaseProjection.project (A 10 1010)).val
  let v2 := (ExactBaseProjection.project (A 10 1012)).val
  if h0 : v0 < 2 ^ 30 then
    if h1 : v1 < 2 ^ 30 then
      if h2 : v2 < 2 ^ 30 then
        some (⟨v0, h0⟩, ⟨v1, h1⟩, ⟨v2, h2⟩)
      else none
    else none
  else none

/-- Embedded 30-bit natural values in the three trace cells decode exactly. -/
theorem decode_of_values (A : Trace WideExact)
    (v0 v1 v2 : Fin (2 ^ 30))
    (h0 : A 10 1008 = (v0.val : WideExact))
    (h1 : A 10 1010 = (v1.val : WideExact))
    (h2 : A 10 1012 = (v2.val : WideExact)) :
    decode A = some (v0, v1, v2) := by
  have hp0 : v0.val < P := Nat.lt_trans v0.isLt (by norm_num [P])
  have hp1 : v1.val < P := Nat.lt_trans v1.isLt (by norm_num [P])
  have hp2 : v2.val < P := Nat.lt_trans v2.isLt (by norm_num [P])
  have hproj0 : ExactBaseProjection.project (A 10 1008) = (v0.val : M31Exact) := by
    rw [h0, ← map_natCast ExactBaseProjection.embed v0.val]
    exact ExactBaseProjection.project_embed _
  have hproj1 : ExactBaseProjection.project (A 10 1010) = (v1.val : M31Exact) := by
    rw [h1, ← map_natCast ExactBaseProjection.embed v1.val]
    exact ExactBaseProjection.project_embed _
  have hproj2 : ExactBaseProjection.project (A 10 1012) = (v2.val : M31Exact) := by
    rw [h2, ← map_natCast ExactBaseProjection.embed v2.val]
    exact ExactBaseProjection.project_embed _
  have hv0 : (ExactBaseProjection.project (A 10 1008)).val = v0.val := by
    rw [hproj0, ZMod.val_natCast_of_lt hp0]
  have hv1 : (ExactBaseProjection.project (A 10 1010)).val = v1.val := by
    rw [hproj1, ZMod.val_natCast_of_lt hp1]
  have hv2 : (ExactBaseProjection.project (A 10 1012)).val = v2.val := by
    rw [hproj2, ZMod.val_natCast_of_lt hp2]
  simp [decode, hv0, hv1, hv2, v0.isLt, v1.isLt, v2.isLt]

#print axioms decode_of_values

end AspisR1.TraceValueDecode
