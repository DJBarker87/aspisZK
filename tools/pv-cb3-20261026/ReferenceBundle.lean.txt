import R1Z.PV_CB3_Op249Staged
import R1Z.PV_CB3_Op258Staged
import R1Z.PV_CB3_GammaConstructor
import R1Z.PV_CB3_GammaNonzero
import R1Z.PV_CB3_Op258Outcome
import R1Z.PV_CB3_Op258FoldAll
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_ReferenceBundle
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

/-- Reference-only selections. Both native P6 associations remain separate
open obligations. The published CallbackBundle is unchanged. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  PV_CB3_Op249Staged.selected (PV_CB3_Op258Staged.selected ops)

theorem sampler_reference (ops : ExternalFuns) (block : Array U8 32#usize) :
    (selected ops).op249 block = ok (PV_CB3_StagedGammaRank.result block) :=
  PV_CB3_StagedGammaRank.source block

theorem sampler_nonzero (ops : ExternalFuns) (block : Array U8 32#usize) :
    (selected ops).op249 block ≠ ok PV_CB3_GammaNonzero.zero :=
  PV_CB3_GammaNonzero.source_nonzero block

theorem pole_failure (ops : ExternalFuns) (values : PV_CB3_Op258Fold.Rows)
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31) :
    (selected ops).op258 values masks chi = fail .arrayOutOfBounds ↔
      1024 < values.val.length := PV_CB3_Op258Outcome.failure_iff values masks chi

theorem pole_truth (ops : ExternalFuns) (values : PV_CB3_Op258Fold.Rows)
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31) :
    (selected ops).op258 values masks chi = ok true ↔ values.val.length ≤ 1024 ∧
      ∀ i : Nat, i<values.val.length →
        PV_CB3_Op258Fold.keep values masks chi (PV_CB3_PoleAdvance.advance i 0#usize) = true :=
  PV_CB3_Op258FoldAll.all_inputs values masks chi
#print axioms sampler_reference
#print axioms sampler_nonzero
#print axioms pole_failure
#print axioms pole_truth
end R1Z.PV_CB3_ReferenceBundle
