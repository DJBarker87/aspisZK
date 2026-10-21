import S8OwnedP6R14Backend
import S8OwnedP6StrictScanModel
import S8OwnedP6Residue

/-! Named checked reference/model certificate. Source correspondence is
provided separately by the P6 Kani receipts and their stated domains. -/
set_option autoImplicit false
noncomputable section
namespace S8OwnedP6Certificate
open Aeneas Aeneas.Std Result
open S8OwnedP6 S8OwnedP6ValueModel S8OwnedP6Finish S8OwnedP6Scan

structure ReferenceCertificate : Prop where
  finish : ∀ raw old, old.length≤raw.length →
    ∃ out : Weights, finish_owned raw old=.ok out ∧ out.length=old.length ∧
      ∀ j, j<old.length → out.val[j]?=(raw.val[j]?).map modelValue
  scan : ∀ bytes : Slice U8,
    ∃ out : Status, check_values_owned bytes=.ok out ∧
      (out=.Ok () ↔ ∀ j, j<bytes.val.length/16 →
        S8OwnedP6StrictScanModel.CanonicalChunk bytes j) ∧
      (out=.Ok () ∨ out=.Err .NonCanonical)
  residue : ∀ (row : Row) (power : Q) (basis : U32) (terms : Nat),
    (∀ j : Fin 4, (coordinate power j).val<2^31-1) → basis.val<2^31-1 →
    (∀ j : Fin 4, (rowAt row j).val<2^34+(terms%4)*(2^31-2)^2) →
    ∃ out : Row, residue_owned row power basis (decide (terms%4=3))=.ok out ∧
      ∀ j : Fin 4, (rowAt out j).val=
        AspisR1BatchedFoldSourceStep.sourcePush terms (rowAt row j).val
          ((coordinate power j).val*basis.val)
  reducer_repin : ∀ x : U64, aspis_core.field.M31.reduce_u64 x=
    AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x

/-- Arbitrary-size emitted reference loops, the full residue row, and the
precise existing R14 reducer model all have supplying theorems. -/
theorem reference_model : ReferenceCertificate :=
  ⟨finish_total_model,S8OwnedP6StrictScanModel.strict_scan_total,
    S8OwnedP6Residue.residue_total_model,S8OwnedP6R14Backend.reducer_repin⟩

#print axioms reference_model
end S8OwnedP6Certificate
