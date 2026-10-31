import R1Z.PV_RDCD4_ParserWindows
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_V197
open Aeneas Aeneas.Std Result PV_RDCD4_BytesSource
/-- Explicit complete-Result reference. The second length check remains after
c0's None short circuit. Inputs of length8..15 can therefore return None or
panic exactly as the original source does; no eager16-byte guard is added. -/
def reference (bytes : List U8) : Result (Option Q) :=
  if 8 ≤ bytes.length then do
    let c0 ← cm (PV_RDCD4_SliceRange194.window bytes 0 8)
    match c0 with
    | none => ok none
    | some c0 =>
      if 16 ≤ bytes.length then do
        let c1 ← cm (PV_RDCD4_SliceRange194.window bytes 8 16)
        match c1 with
        | none => ok none
        | some c1 => ok (some ⟨c0,c1⟩)
      else fail .arrayOutOfBounds
  else fail .arrayOutOfBounds

theorem source_reference (bytes : List U8) : qm bytes=reference bytes := by
  unfold qm reference
  by_cases h8 : 8 ≤ bytes.length
  · rw [if_pos h8,PV_RDCD4_SliceRange194.success bytes 0 8 (by omega) h8,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro result _
    cases result with
    | none => rfl
    | some c0 =>
      by_cases h16 : 16 ≤ bytes.length
      · rw [if_pos h16,PV_RDCD4_SliceRange194.success bytes 8 16 (by omega) h16,bind_tc_ok]
      · rw [if_neg h16,PV_RDCD4_SliceRange194.oversized bytes 8 16 (by omega)]
        try rfl
  · rw [if_neg h8,PV_RDCD4_SliceRange194.oversized bytes 0 8 (by omega)]
    try rfl

theorem short_failure (bytes : List U8) (h : bytes.length < 8) :
    qm bytes=fail .arrayOutOfBounds := by
  rw [source_reference,reference,if_neg (by omega)]

/-- Returned values contain no borrow; input storage is unchanged at this
owned value boundary. The rejected extractor/loan-validation route is unused. -/
theorem frame (bytes : List U8) :
    (do let out ← qm bytes;ok (out,bytes))=
      (do let out ← reference bytes;ok (out,bytes)) := by rw [source_reference]
#print axioms source_reference
#print axioms short_failure
#print axioms frame
end R1Z.PV_RDCD4_V197
