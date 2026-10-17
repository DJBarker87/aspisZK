import RawPoseidonExtensionWords
import RawPoseidonRowField
import ExtractedMaskQM31Exact

/-! Source reassembly of arbitrary U64 limb vectors into the exact tower.
This composes the existing source word/reducer theorem with the existing
symbolic decodeWords_mod theorem; no field multiplication is expanded. -/
set_option autoImplicit false
namespace AspisR1.PoseidonRawLimbReassembly
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.RawPoseidonExtensionWords
open AspisR1.RawPoseidonRowField
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

theorem source_success (xs : Limbs) :
    ∃ out : field.QM31, state_only_poseidon.extension_from_raw_limbs xs = .ok out ∧
      Canonical out ∧ Decode out = decodeWords (fun j => (limbAt xs j).val) := by
  obtain ⟨out,hrun,hcanonical,hwords⟩ := extension_from_raw_limbs_words xs
  have h0 := congrArg (fun w : (Nat × Nat) × (Nat × Nat) => w.1.1) hwords
  have h1 := congrArg (fun w : (Nat × Nat) × (Nat × Nat) => w.1.2) hwords
  have h2 := congrArg (fun w : (Nat × Nat) × (Nat × Nat) => w.2.1) hwords
  have h3 := congrArg (fun w : (Nat × Nat) × (Nat × Nat) => w.2.2) hwords
  change out.c0.a.val = (limbAt xs 0).val % AspisR1.ExtractedMaskTowerAdd.P at h0
  change out.c0.b.val = (limbAt xs 1).val % AspisR1.ExtractedMaskTowerAdd.P at h1
  change out.c1.a.val = (limbAt xs 2).val % AspisR1.ExtractedMaskTowerAdd.P at h2
  change out.c1.b.val = (limbAt xs 3).val % AspisR1.ExtractedMaskTowerAdd.P at h3
  have hdecode : Decode out = decodeWords
      (fun j => (limbAt xs j).val % AspisV8R15.ExactTowerBase.P) := by
    ext <;> simp only [Decode,AspisR1.ExtractedMaskQM31Exact.decode,decodeWords,h0,h1,h2,h3]
  refine ⟨out,hrun,hcanonical,?_⟩
  exact hdecode.trans (decodeWords_mod (fun j => (limbAt xs j).val))

#print axioms source_success
end AspisR1.PoseidonRawLimbReassembly
