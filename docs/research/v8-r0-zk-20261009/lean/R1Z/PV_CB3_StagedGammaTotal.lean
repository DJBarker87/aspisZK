import R1Z.PV_CB3_StagedComposition
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedGammaTotal
open Aeneas Aeneas.Std Result
open PV_CB3_StagedComposition

theorem carry_total (digits : Array U32 8#usize) (a : U32) :
    ∃ out, PV_CB3_StagedSource.staged_reference.carry digits a = ok out := by
  unfold PV_CB3_StagedSource.staged_reference.carry
  repeat' first
    | exact ⟨_,rfl⟩
    | exact read_total _ _ (by decide)
    | exact PV_CB3_StagedWord.carry_total _ _
    | apply bind_total
    | rintro ⟨x,y⟩
    | intro x

/-- Complete Result of the extracted owned reference, over all 256 input bits.
This is not yet the shipped sampler source law: its native P6 gate is open. -/
theorem gamma_total (block : Array U8 32#usize) :
    ∃ out, PV_CB3_StagedSource.staged_reference.gamma block = ok out := by
  unfold PV_CB3_StagedSource.staged_reference.gamma
  repeat' first
    | exact ⟨_,rfl⟩
    | exact words_total _
    | exact pass_total _
    | exact read_total _ _ (by decide)
    | exact carry_total _ _
    | exact PV_CB3_StagedTotal.constructor_total _ _
    | apply bind_total
    | rintro ⟨x,y⟩
    | intro x
    | split
#print axioms carry_total
#print axioms gamma_total
end R1Z.PV_CB3_StagedGammaTotal
