import R1Z.PV_RunJoin_BatchInstalled48
import R1Z.PV_RunJoin_GammaPowers44
import R1Z.PV_DL_EncoderSelected
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EncoderGammaFields49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46

theorem candidate_powers [ExternalTypes] (ops : ExternalFuns) :
    (ProverRwP6BodyCandidate.selected ops).op254=ops.op254 := rfl

theorem incoming_powers [ExternalTypes] (ops : ExternalFuns) :
    (PV_DL_EncoderSelected.selected (PV_RunJoin_GammaPowers44.inputs ops)).op254=
      (PV_RunJoin_GammaPowers44.inputs ops).op254 := rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem powers (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op254 (types base) (selected base heap box ops)=ops.op254 := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_254]
  exact @candidate_powers (types base) ops

attribute [local irreducible] selected PV_B2_F_RawNative.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize))
    (g : aspis_core.field.wide_exact.WideExact) :
    @prover.opening_batch (types base) (selected base heap box
      (@PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops))) coefficients g=
    @prover.opening_batch (types base) (selected base heap box
      (@PV_RunJoin_GammaPowers44.inputs (types base) ops)) coefficients g := by
  apply @PV_RunJoin_BatchCongruence48.complete (types base)
  · exact (PV_RunJoin_InactiveFields48.zero base heap box _).trans
      (PV_RunJoin_InactiveFields48.zero base heap box _).symm
  · exact (PV_RunJoin_BatchFields48.mul base heap box _).trans
      ((@PV_RunJoin_BatchFields48.candidate_mul (types base) _).trans
        ((@PV_RunJoin_BatchFields48.candidate_mul (types base) _).symm.trans
          (PV_RunJoin_BatchFields48.mul base heap box _).symm))
  · exact (PV_RunJoin_InactiveFields48.add base heap box _).trans
      (PV_RunJoin_InactiveFields48.add base heap box _).symm
  · exact (powers base heap box _).trans
      ((@incoming_powers (types base) ops).trans (powers base heap box _).symm)
#print axioms candidate_powers
#print axioms incoming_powers
#print axioms powers
#print axioms complete
end R1Z.PV_RunJoin_EncoderGammaFields49
