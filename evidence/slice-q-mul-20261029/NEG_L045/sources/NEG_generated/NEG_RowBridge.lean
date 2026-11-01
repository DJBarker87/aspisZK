import NEG_RowStepAssociation
set_option autoImplicit false
noncomputable section
namespace NEG_RowBridge
open Aeneas Aeneas.Std Result
abbrev Power := NEG_RowAssociation.Power
abbrev modelPower (p : Power) := Port26ROW.toK (NEG_RowAssociation.toOld p)

theorem total (row : Array U64 4#usize) (p : Power) (basis : U32) (flush : Bool)
    (safe : ∀ j raw, j.val<4 → Array.index_usize row j=ok raw →
      raw.val+(S7Kani2OwnedRow.limb (modelPower p) j).val*basis.val<2^64) :
    ∃ out, NEG_RowIsolated.update_residue_row row p basis flush=ok out := by
  rw [NEG_RowAssociation.emitted_to_owned]
  exact S7Kani2OwnedRow.row_total row (modelPower p) basis flush safe

theorem from_phase (row : Array U64 4#usize) (p : Power) (basis : U32) (terms : Nat)
    (canonical : ∀ j : Usize, j.val<4 →
      (S7Kani2OwnedRow.limb (modelPower p) j).val<2147483647)
    (basisCanonical : basis.val<2147483647)
    (phase : ∀ j raw, j.val<4 → Array.index_usize row j=ok raw →
      raw.val<2^34+(terms%4)*(2^31-2)^2) :
    ∃ out, NEG_RowIsolated.update_residue_row row p basis (decide (terms%4=3))=ok out := by
  apply total
  intro j raw hj read
  exact S7OwnedP6ScalarProof.phase_bound raw _ basis (terms%4)
    (Nat.mod_lt _ (by decide)) (canonical j hj) basisCanonical (phase j raw hj read)

#print axioms total
#print axioms from_phase
end NEG_RowBridge
end
