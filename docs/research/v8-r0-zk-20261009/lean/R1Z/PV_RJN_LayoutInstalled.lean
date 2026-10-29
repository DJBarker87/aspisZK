import R1Z.PV_RJN_Producers
import R1Z.ProverRwDictionaryLayoutValues
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJN_LayoutInstalled
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PublishSkeleton54 PV_RunJoin_WeightInstalled46
open PV_RJN_Producers
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

def header : Bytes := bytes [82#u8,49#u8,80#u8,51#u8,67#u8,66#u8,49#u8,56#u8] ++
  bytes [2#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]

/-- Literal plan facts that the actual Data/Plan producer supplies. -/
def PV_RJN_Producer_PlanLayout {I : Type} [ExternalTypes] (runs : I → Run) : Prop :=
  ∀ i, (runs i).plan.proofBytes=57607 ∧ (runs i).plan.offOpenings=10055 ∧
    (runs i).plan.offNodes=28359 ∧ (runs i).plan.header=header

def PV_RJN_Producer_FrontLengths {I : Type} [ExternalTypes] (runs : I → Run) : Prop :=
  ∀ i, (runs i).plan.header.length=16 ∧ (runs i).plan.semantic.length=7015 ∧ (runs i).plan.claim.length=464

theorem front_room {I : Type} [ExternalTypes] [ExternalFuns] (runs : I → Run)
    (producer : PV_RJN_Producer_FrontLengths runs) : PV_RJN_Producer_FrontRoom runs := by
  intro i
  obtain ⟨hh,hs,hc⟩ := producer i
  rw [hh,hs,hc]
  scalar_tac

theorem primitive_size [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op242 _ (ProverRwP6BodyCandidate.selected ops)=ok 57607#usize := by
  have entry : @ExternalFuns.op242 _ (ProverRwP6BodyCandidate.selected ops)=
      ProverRwDictionaryLayoutSource.compact.PROOF_BYTES := by
    unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
    rfl
  rw [entry]
  exact ProverRwDictionaryLayoutTotal.r22_compact_PROOF_BYTES_total

theorem primitive_openings [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op244 _ (ProverRwP6BodyCandidate.selected ops)=ok 10055#usize := by
  have entry : @ExternalFuns.op244 _ (ProverRwP6BodyCandidate.selected ops)=
      ProverRwDictionaryLayoutSource.compact.OFF_OPENINGS := by
    unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
    rfl
  rw [entry]
  exact ProverRwDictionaryLayoutTotal.r22_compact_OFF_OPENINGS_total

theorem primitive_nodes [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op243 _ (ProverRwP6BodyCandidate.selected ops)=ok 28359#usize := by
  have entry : @ExternalFuns.op243 _ (ProverRwP6BodyCandidate.selected ops)=
      ProverRwDictionaryLayoutSource.compact.OFF_NODES := by
    unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
    rfl
  rw [entry]
  exact ProverRwDictionaryLayoutTotal.r22_compact_OFF_NODES_total

theorem primitive_magic [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op245 _ (ProverRwP6BodyCandidate.selected ops)=ok ProverRwDictionaryLayoutSource.compact.MAGIC := by
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem primitive_tag [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op234 _ (ProverRwP6BodyCandidate.selected ops) .S2=ok 2#u8 := by
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem actual (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) {I : Type} (runs : I → @Run (types base))
    (producer : PV_RJN_Producer_PlanLayout runs) :
    @PV_RJN_Producer_Layout (types base) (selected base heap box ops) I runs := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  intro i
  obtain ⟨hsize,hopen,hnodes,hheader⟩ := producer i
  refine ⟨57607#usize,10055#usize,28359#usize,ProverRwDictionaryLayoutSource.compact.MAGIC,2#u8,
    ?_,?_,?_,?_,?_,hsize,hopen,hnodes,hheader⟩
  · change @ExternalFuns.op242 (types base) (selected base heap box ops)=_
    unfold selected
    rw [PV_B2_F_RawNative.preserved_242]
    exact primitive_size ops
  · change @ExternalFuns.op244 (types base) (selected base heap box ops)=_
    unfold selected
    rw [PV_B2_F_RawNative.preserved_244]
    exact primitive_openings ops
  · change @ExternalFuns.op243 (types base) (selected base heap box ops)=_
    unfold selected
    rw [PV_B2_F_RawNative.preserved_243]
    exact primitive_nodes ops
  · change @ExternalFuns.op245 (types base) (selected base heap box ops)=_
    unfold selected
    rw [PV_B2_F_RawNative.preserved_245]
    exact primitive_magic ops
  · change @ExternalFuns.op234 (types base) (selected base heap box ops) .S2=_
    unfold selected
    rw [PV_B2_F_RawNative.preserved_234]
    exact primitive_tag ops
#print axioms PV_RJN_Producer_PlanLayout
#print axioms PV_RJN_Producer_FrontLengths
#print axioms front_room
#print axioms primitive_size
#print axioms primitive_openings
#print axioms primitive_nodes
#print axioms primitive_magic
#print axioms primitive_tag
#print axioms actual
end R1Z.PV_RJN_LayoutInstalled
