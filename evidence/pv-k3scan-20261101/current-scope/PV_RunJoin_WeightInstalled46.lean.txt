import R1Z.PV_RunJoin_WeightCarrier46
import R1Z.ProverRwP6BodyCandidate
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WeightInstalled46
open Aeneas Aeneas.Std Result ProverRwFull
abbrev types := PV_B2_F_RawNative.types
abbrev Heap := PV_B2_F_RawNative.HeapRequest
abbrev Box := PV_B2_F_RawNative.BoxRequest

def selected (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) : @ExternalFuns (types base) :=
  PV_B2_F_RawNative.selected base heap box (@ProverRwP6BodyCandidate.selected (types base) ops)

attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected

theorem constructor (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op252 (types base) (selected base heap box ops)=
      PV_B2_F_ResourceFamilies.boxOriginal box := by
  unfold selected
  change @ExternalFuns.op252 (types base)
    (PV_B2_F_ResourceFamilies.selected base heap box _) = _
  funext v alpha z
  exact PV_B2_F_ResourceFamilies.selected_box base heap box _ v alpha z

theorem materialize (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op251 (types base) (selected base heap box ops)=
      PV_B2_F_ResourceFamilies.heapOriginal heap := by
  unfold selected
  change @ExternalFuns.op251 (types base)
    (PV_B2_F_ResourceFamilies.selected base heap box _) = _
  funext w kappa
  exact PV_B2_F_ResourceFamilies.selected_heap base heap box _ w kappa

theorem raw (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op253 (types base) (selected base heap box ops)=
      PV_B2_F_RawNative.originalCallback := by
  funext w kind j
  exact PV_B2_F_RawNative.source base heap box _ w kind j

#print axioms constructor
#print axioms materialize
#print axioms raw
end R1Z.PV_RunJoin_WeightInstalled46
