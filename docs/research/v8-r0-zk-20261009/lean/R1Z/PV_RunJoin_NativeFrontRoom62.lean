import R1Z.PV_RunJoin_NativeActual62
import R1Z.PV_RunJoin_FrontProjection62
import R1Z.PV_RunJoin_ActualFrontRoom61
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeFrontRoom62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual62
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected

theorem logical (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    @compact.LOGICAL_SEMANTIC (types base) (opsNative base heap box ops)=ok 13831#usize := by
  change @ExternalFuns.op241 (types base) (opsNative base heap box ops)=_
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_241]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  change ProverRwDictionaryLayoutSource.compact.LOGICAL_SEMANTIC=ok 13831#usize
  exact ProverRwDictionaryLayoutTotal.r22_compact_LOGICAL_SEMANTIC_total

/-- The original front-room producer inequality, with no successful-publication
or Fields guard. It even covers the total malformed-Phase fallbacks. -/
theorem complete (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_ActualFrontRoom61.FrontRoom (types base) (opsNative base heap box ops) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  intro p
  have hs := PV_RunJoin_FrontProjection62.publication p.val
    PV_RunJoin_ActualPlanSources59.compactSemantic (55*13831)
    (fun publication => PV_RunJoin_FrontProjection62.semantic publication (logical base heap box ops))
  have hc := PV_RunJoin_FrontProjection62.publication p.val
    PV_RunJoin_ActualPlanSources59.compactClaim (Usize.max/2) PV_RunJoin_CompactUniversal62.claim
  have hh : (PV_RunJoin_ActualRun.plans p.val).header.length=16 := rfl
  change (PV_RunJoin_ActualRun.plans p.val).header.length+
    (PV_RunJoin_ActualRun.plans p.val).semantic.length+
    (PV_RunJoin_ActualRun.plans p.val).claim.length≤Usize.max
  rw [hh]
  change (PV_RunJoin_ActualRun.plans p.val).semantic.length≤55*13831 at hs
  change (PV_RunJoin_ActualRun.plans p.val).claim.length≤Usize.max/2 at hc
  have cap : 2000000≤Usize.max := by scalar_tac
  omega

theorem publishOrder (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_PublishProduced60.PV_RunJoin_Link_PublishOrder (types base) (opsNative base heap box ops) :=
  PV_RunJoin_ActualFrontRoom61.specialize (baseTypes base) heap box (residual base ops)
    (complete base heap box ops)

#print axioms logical
#print axioms complete
#print axioms publishOrder
end R1Z.PV_RunJoin_NativeFrontRoom62
