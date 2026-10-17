import AspisR1.PoseidonPow5SourceExact
import ExtractedMaskM31AddSub

/-! Factored exact per-cell computation from full_round_m31_constants(_packed).
Array index/mutation binding and loop traversal are separate source steps. -/
set_option autoImplicit false
namespace AspisR1.PoseidonM31ConstantPow5
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Exact := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev P := AspisR1.ExtractedMaskM31AddSub.P

def updated (value : QM) (m : field.M31) : QM :=
  { value with c0 := { value.c0 with a := m } }
def source (value : QM) (constant1 : field.M31) : Result QM := do
  let m ← field.M31.add value.c0.a constant1
  state_only_poseidon.pow5 (updated value m)

theorem source_success (value : QM) (constant1 : field.M31)
    (hvalue : Canonical value) (hconstant : constant1.val < P) :
    ∃ out : QM, source value constant1 = .ok out ∧ Canonical out ∧
      Decode out = R0P.poseidonPow5 (Decode value + (constant1.val : Exact)) := by
  obtain ⟨m,hm,hmVal,hmCan⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_add_mod value.c0.a constant1 hvalue.1.1 hconstant
  have hupdated : Canonical (updated value m) := ⟨⟨hmCan,hvalue.1.2⟩,hvalue.2⟩
  have hdecode : Decode (updated value m) = Decode value + (constant1.val : Exact) := by
    ext <;> simp [Decode,AspisR1.ExtractedMaskQM31Exact.decode,updated,hmVal,
      P,AspisR1.ExtractedMaskM31AddSub.P,AspisV8R15.ExactTowerBase.P,ZMod.natCast_mod]
  obtain ⟨out,hout,houtCan,houtDec⟩ :=
    AspisR1.PoseidonPow5SourceExact.source_success (updated value m) hupdated
  change Decode out = R0P.poseidonPow5 (Decode (updated value m)) at houtDec
  refine ⟨out,?_,houtCan,?_⟩
  · simp only [source,hm,bind_tc_ok,hout]
  · rw [hdecode] at houtDec
    exact houtDec

#print axioms source_success
end AspisR1.PoseidonM31ConstantPow5
