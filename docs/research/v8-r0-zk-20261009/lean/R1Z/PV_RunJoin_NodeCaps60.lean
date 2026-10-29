import R1Z.PV_RJN_LayoutInstalled
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NodeCaps60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem primitive [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op237 _ (ProverRwP6BodyCandidate.selected ops)=
      ok ProverRwDictionaryLayoutSource.compact.SLOT_NODES := by
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem installed (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @compact.SLOT_NODES (types base) (selected base heap box ops)=
      ok ProverRwDictionaryLayoutSource.compact.SLOT_NODES := by
  change @ExternalFuns.op237 (types base) (selected base heap box ops)=_
  unfold selected
  rw [PV_B2_F_RawNative.preserved_237]
  exact primitive ops

/-- Source padding capacities; no node traversal is evaluated. -/
theorem values : ProverRwDictionaryLayoutSource.compact.SLOT_NODES.val=
    [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize] := rfl

#print axioms primitive
#print axioms installed
#print axioms values
end R1Z.PV_RunJoin_NodeCaps60
