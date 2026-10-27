import PV_B1_Orig258_Op258Fold
import PV_B1_Orig258_Op258Outside
import PV_B1_Orig258_PoleAdvance
set_option autoImplicit false
noncomputable section
namespace PV_B1_Orig258_Op258FoldAll
open Aeneas Aeneas.Std Result PV_B1_258
open PV_B1_Orig258_Op258Fold PV_B1_Orig258_PoleAdvance

theorem scan_truth (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (n : Nat) (row : Usize) : scan values masks chi n row = true ↔
      ∀ i : Nat, i<n → keep values masks chi (advance i row) = true := by
  induction n generalizing row with
  | zero => simp only [scan]; simp
  | succ n ih =>
    rw [scan,Bool.and_eq_true_iff,ih]
    constructor
    · rintro ⟨head,tail⟩ i hi
      cases i with
      | zero => simpa only [advance] using head
      | succ i => simpa only [advance] using tail i (by omega)
    · intro all
      constructor
      · simpa only [advance] using all 0 (by omega)
      · intro i hi
        simpa only [advance] using all (i+1) (by omega)

theorem source_truth (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (bound : values.val.length ≤ 1024) :
    PV_B1_PoleOriginal.reference.all_slots_clear values masks chi = ok true ↔
      ∀ i : Nat, i<values.val.length → keep values masks chi (advance i 0#usize) = true := by
  rw [source_scan values masks chi bound]
  simp only [Result.ok.injEq,scan_truth]

/-- All slice lengths, preserving the oversized failure path. Reference only. -/
theorem all_inputs (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31) :
    PV_B1_PoleOriginal.reference.all_slots_clear values masks chi = ok true ↔
      values.val.length ≤ 1024 ∧
      ∀ i : Nat, i<values.val.length → keep values masks chi (advance i 0#usize) = true := by
  by_cases h : values.val.length ≤ 1024
  · rw [source_truth values masks chi h]
    exact ⟨fun hp => ⟨h,hp⟩,fun hp => hp.2⟩
  · rw [PV_B1_Orig258_Op258Outside.source_failure values masks chi (by omega)]
    constructor
    · intro impossible; cases impossible
    · rintro ⟨bound,_⟩; exact False.elim (h bound)
#print axioms scan_truth
#print axioms source_truth
#print axioms all_inputs
end PV_B1_Orig258_Op258FoldAll
