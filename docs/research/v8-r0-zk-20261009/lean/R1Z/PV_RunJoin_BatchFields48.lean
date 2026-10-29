import R1Z.PV_RunJoin_InactiveFields48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BatchFields48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46

theorem candidate_mul [ExternalTypes] (ops : ExternalFuns) :
    (ProverRwP6BodyCandidate.selected ops).op47=ProverRwDictionaryTower.wMul := rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem zero (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op42 (types base) (selected base heap box ops)=
      (@ProverRwP6BodyCandidate.selected (types base) ops).op42 :=
  (PV_RunJoin_InactiveFields48.zero base heap box ops).trans
    (@PV_RunJoin_InactiveFields48.candidate_zero (types base) ops).symm

theorem add (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op46 (types base) (selected base heap box ops)=
      (@ProverRwP6BodyCandidate.selected (types base) ops).op46 :=
  (PV_RunJoin_InactiveFields48.add base heap box ops).trans
    (@PV_RunJoin_InactiveFields48.candidate_add (types base) ops).symm

theorem mul (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op47 (types base) (selected base heap box ops)=
      (@ProverRwP6BodyCandidate.selected (types base) ops).op47 := by
  unfold selected
  exact PV_B2_F_RawNative.preserved_47 base heap box _

theorem powers (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op254 (types base) (selected base heap box ops)=
      @ExternalFuns.op254 (types base) (@ProverRwP6BodyCandidate.selected (types base) ops) := by
  unfold selected
  exact PV_B2_F_RawNative.preserved_254 base heap box _
#print axioms candidate_mul
#print axioms zero
#print axioms add
#print axioms mul
#print axioms powers
end R1Z.PV_RunJoin_BatchFields48
