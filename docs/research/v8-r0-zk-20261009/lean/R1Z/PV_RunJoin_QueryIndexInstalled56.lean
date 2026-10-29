import R1Z.PV_RunJoin_QueryInvalidIndex56
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryIndexInstalled56
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem primitive [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op75 _ (ProverRwP6BodyCandidate.selected ops)=ProverRwDictionaryDomain.fibreNew := by
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem installed (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op75 (types base) (selected base heap box ops)=ProverRwDictionaryDomain.fibreNew := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_75]
  exact primitive ops

theorem rejected (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @aspis_core.r0.domain.FibreIndex.new (types base) (selected base heap box ops) 262144#usize=ok (.Err .IndexOutOfRange) := by
  rw [installed]
  simp only [ProverRwDictionaryDomain.fibreNew,lt_self_iff_false,if_false]

#print axioms primitive
#print axioms installed
#print axioms rejected
end R1Z.PV_RunJoin_QueryIndexInstalled56
