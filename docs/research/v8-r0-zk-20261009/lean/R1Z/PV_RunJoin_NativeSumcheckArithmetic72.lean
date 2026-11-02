import R1Z.PV_RunJoin_NativeQuarticTotal69
import R1Z.PV_RunJoin_PolyEvalTotal72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSumcheckArithmetic72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
abbrev Q := aspis_core.field.QM31
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem boundary_source :
    @aspis_core.state_only_sumcheck.state_only_boundary_sum (types base)
      (opsNative base heap box ops runtime world)=ProverRwP6BoundarySource.boundary_flat := by
  change @ExternalFuns.op120 (types base) (opsNative base heap box ops runtime world)=_
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_120]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem boundary (poly : Array Q 28#usize) :
    ∃ out,@aspis_core.state_only_sumcheck.state_only_boundary_sum (types base)
      (opsNative base heap box ops runtime world) poly=ok out := by
  rw [boundary_source]
  exact ProverRwP6BoundaryTotal.total poly

theorem evaluation_source :
    @aspis_core.state_only_sumcheck.evaluate_state_only_polynomial (types base)
      (opsNative base heap box ops runtime world)=PV_B3_Install121.callback := by
  change @ExternalFuns.op121 (types base) (opsNative base heap box ops runtime world)=_
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_121]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem evaluation (poly : Array Q 28#usize) (x : Q) :
    ∃ out,@aspis_core.state_only_sumcheck.evaluate_state_only_polynomial (types base)
      (opsNative base heap box ops runtime world) poly x=ok out := by
  rw [evaluation_source]
  obtain ⟨out,ho⟩ := PV_RunJoin_PolyEvalTotal72.complete (PV_B3_Carrier117.fromArray poly) (PV_B3_Carrier117.fromQ x)
  exact ⟨PV_B3_Carrier117.toQ out,by simp only [PV_B3_Install121.callback,ho,
    PV_B3_Carrier117.map,PV_B3_ArrayCarrier.resultMap]⟩

#print axioms boundary_source
#print axioms boundary
#print axioms evaluation_source
#print axioms evaluation
end R1Z.PV_RunJoin_NativeSumcheckArithmetic72
