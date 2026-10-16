import ExtractedMaskQM31Exact
import SelectorReconstructIndexModel

/-! A symbolic success/canonicality invariant for the candidate reverse-index
loop, using the exact checked QM31 addition contract at every step. -/
set_option autoImplicit false
namespace AspisR1.SelectorReconstructIndexedCanonical

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskTowerAdd
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM

def checkedReconstructIndexed (view : Nat → QM) : Nat → QM → Result QM
  | 0, acc => .ok acc
  | n + 1, acc => do
      let doubled ← field.QM31.add acc acc
      let next ← field.QM31.add doubled (view n)
      checkedReconstructIndexed view n next

theorem checkedReconstructIndexed_success_canonical
    (view : Nat → QM) (n : Nat) (acc out : QM)
    (hacc : Canonical acc)
    (hview : ∀ i, i < n → Canonical (view i))
    (hrun : checkedReconstructIndexed view n acc = .ok out) :
    Canonical out ∧
    decode out =
      AspisR1.SelectorReconstructIndexModel.reconstructIndexed
        (fun i => decode (view i)) n (decode acc) := by
  induction n generalizing acc out with
  | zero =>
      have hEq : acc = out := by simpa [checkedReconstructIndexed] using hrun
      subst out
      exact ⟨hacc, rfl⟩
  | succ n ih =>
      have hbit : Canonical (view n) := hview n (by omega)
      obtain ⟨doubled, hdoubleRun, hdoubleCanonical, hdoubleDecode⟩ :=
        current_qm_add_exact acc acc hacc hacc
      obtain ⟨next, hnextRun, hnextCanonical, hnextDecode⟩ :=
        current_qm_add_exact doubled (view n) hdoubleCanonical hbit
      have hrun' := hrun
      change (do
        let doubled' ← field.QM31.add acc acc
        let next' ← field.QM31.add doubled' (view n)
        checkedReconstructIndexed view n next') = .ok out at hrun'
      simp only [hdoubleRun, bind_tc_ok, hnextRun, bind_tc_ok] at hrun'
      obtain ⟨houtCanonical, houtDecode⟩ :=
        ih next out hnextCanonical (by intro i hi; exact hview i (by omega)) hrun' 
      refine ⟨houtCanonical, ?_⟩
      calc
        decode out =
            AspisR1.SelectorReconstructIndexModel.reconstructIndexed
              (fun i => decode (view i)) n (decode next) := houtDecode
        _ = AspisR1.SelectorReconstructIndexModel.reconstructIndexed
              (fun i => decode (view i)) n
                (decode acc + decode acc + decode (view n)) := by
              rw [hnextDecode, hdoubleDecode]
        _ = AspisR1.SelectorReconstructIndexModel.reconstructIndexed
              (fun i => decode (view i)) (n + 1) (decode acc) := rfl

#print axioms checkedReconstructIndexed_success_canonical
end AspisR1.SelectorReconstructIndexedCanonical
