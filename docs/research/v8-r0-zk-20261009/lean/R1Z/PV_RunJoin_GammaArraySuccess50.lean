import R1Z.PV_RunJoin_GammaActualInputs50
import R1Z.PV_RunJoin_MappedSuccess50
import R1Z.PV_RunJoin_PrefixImage50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaArraySuccess50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW toW)
open PV_RunJoin_ClaimThread48 (Column W)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (columns : Slice Column) (length : columns.length=29) (g : W) (out : alloc.vec.Vec W)
    (h : @prover.opening_batch (types base)
      (selected base heap box (@PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)))
      columns g=ok out) :
    ∃ a : Array ProverCommitWideOps48.Source 1024#usize,
      ProverCommitGammaOutput53.run (PV_RunJoin_GammaActualInputs50.table columns length) (toW g)=ok a ∧
      out=PV_RunJoin_PrefixFold50.image fromW a ∧ out.length=1024 ∧
      alloc.vec.Vec.deref out=Array.to_slice (amap fromW a) := by
  rw [PV_RunJoin_GammaActualInputs50.complete base heap box ops columns length g] at h
  obtain ⟨a,ha,he⟩ := PV_RunJoin_MappedSuccess50.complete _ _ _ h
  refine ⟨a,ha,he.symm,?_,?_⟩
  · rw [←he];exact PV_RunJoin_PrefixImage50.length _ _
  · rw [←he];exact PV_RunJoin_PrefixImage50.slice _ _
#print axioms complete
end R1Z.PV_RunJoin_GammaArraySuccess50
