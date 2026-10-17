import ExtractedMaskQM31SquareExact
import ExtractedMaskQM31Exact
import R0P.Poseidon

/-! Exact missing generated pow5 declaration from Funs
f1e258056294e84777f56f2a1ea3572329eca52b4bb553bfc6c58027bef1604c,
state_only_poseidon.rs lines 124--127. Existing field primitive owners and
their checked square/multiply arithmetic are reused without replacement. -/
set_option autoImplicit false
namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result

def state_only_poseidon.pow5 (value : field.QM31) : Result field.QM31 := do
  let square ← field.QM31.square value
  let q ← field.QM31.square square
  field.QM31.mul q value
end AspisR1SelectedMaskProbe

namespace AspisR1.PoseidonPow5SourceExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

theorem source_success (value : QM) (hvalue : Canonical value) :
    ∃ out : QM, state_only_poseidon.pow5 value = .ok out ∧ Canonical out ∧
      Decode out = R0P.poseidonPow5 (Decode value) := by
  obtain ⟨square,hsquare,hsquareCan,hsquareDec⟩ :=
    AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact value hvalue
  obtain ⟨fourth,hfourth,hfourthCan,hfourthDec⟩ :=
    AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact square hsquareCan
  obtain ⟨out,hout,houtCan,houtDec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact fourth value hfourthCan hvalue
  change Decode square = Decode value * Decode value at hsquareDec
  change Decode fourth = Decode square * Decode square at hfourthDec
  change Decode out = Decode fourth * Decode value at houtDec
  refine ⟨out,?_,houtCan,?_⟩
  · simp only [state_only_poseidon.pow5,hsquare,bind_tc_ok,hfourth,hout]
  · rw [houtDec,hfourthDec,hsquareDec]
    rfl

#print axioms source_success
end AspisR1.PoseidonPow5SourceExact
