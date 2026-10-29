import R1Z.PV_RunJoin_GammaBatchActual50
import R1Z.PV_RunJoin_ClaimEvaluationActual50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaActualInputs50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW toW)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_GammaSourceCell50 (Columns)
open PV_RunJoin_ClaimThread48 (Column W)

def table (columns : Slice Column) (length : columns.length=29) : Columns :=
  ⟨columns.val.map (amap toW),by rw [List.length_map];exact length⟩

theorem native (columns : Slice Column) (length : columns.length=29) :
    Array.to_slice (amap (amap fromW) (table columns length))=columns := by
  apply Subtype.ext
  change (columns.val.map (amap toW)).map (amap fromW)=columns.val
  rw [List.map_map]
  have inverse : ((amap fromW) ∘ (amap toW) : Column → Column)=id :=
    funext PV_RunJoin_ClaimEvaluationActual50.array_roundtrip
  rw [inverse,List.map_id]

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (columns : Slice Column) (length : columns.length=29) (g : W) :
    let incoming := @PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)
    @prover.opening_batch (types base) (selected base heap box incoming) columns g=
      mapResult (PV_RunJoin_PrefixFold50.image fromW) (ProverCommitGammaOutput53.run (table columns length) (toW g)) := by
  have h := PV_RunJoin_GammaBatchActual50.complete base heap box ops (table columns length) (toW g)
  rw [native,ProverRwDictionaryTower.w_roundtrip] at h
  exact h
#print axioms table
#print axioms native
#print axioms complete
end R1Z.PV_RunJoin_GammaActualInputs50
