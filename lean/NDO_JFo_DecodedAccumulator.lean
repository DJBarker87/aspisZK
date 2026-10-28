import NDO_JFo_AccumulatorState
import RPt_JFq_Rhs
import RPt_JFq_Power
import NDO_JFo_AuthBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_DecodedAccumulator
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCompactDraft
open MultiproofConeCanonical OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
open CheckpointBytes4ReaderFields CheckpointBytes5Output

def value : verifier.Accumulator := ⟨JFo_Weights.value,JFq_Rhs.scalar,JFq_Power.scalar,10#usize⟩

theorem header : slice (bytesOf JFx_NativeBytes.checkpoint.val) 0 16=
    OraclePortPhysicalFrameDraft.magic ++ [2,10,1,0,0,0,0,0] := by
  simp only [slice,bytesOf,List.drop_zero,← List.map_take,JFo_AuthBytes.first16]
  rfl

theorem source : decodeAccumulator (bytesOf JFx_NativeBytes.checkpoint.val)=
    some (accumulator value) := by
  have wSize : JFo_Weights.value.val.length=64 := JFo_Weights.length
  have ckSize : JFx_NativeBytes.checkpoint.val.length=1768 := JFx_NativeBytes.checkpointBytes_length
  obtain ⟨rhs,readRhs,rhsEq,_,_⟩ := CheckpointBytes4ReaderFields.e_success
    (JFq_Raw.reader 664#usize) (JFq_Raw.reader 696#usize) JFq_Rhs.scalar
    (by change 664+32≤JFx_NativeBytes.checkpoint.val.length;rw [ckSize];decide)
    JFq_Rhs.source
  obtain ⟨power,readPower,powerEq,_,_⟩ := CheckpointBytes4ReaderFields.k_success
    (JFq_Raw.reader 696#usize) (JFq_Raw.reader 712#usize) JFq_Power.scalar
    (by change 696+16≤JFx_NativeBytes.checkpoint.val.length;rw [ckSize];decide)
    JFq_Power.source
  have restored := JFo_Weights.source JFo_Weights.value JFo_Weights.length
  obtain ⟨model,readModel,modelEq,_⟩ := CheckpointBytes4SectionContents.weights_contents
    JFx_NativeBytes.checkpoint 712#usize 1736#usize JFo_Weights.value JFo_Weights.value
    (by rw [wSize];change 712+64*16≤JFx_NativeBytes.checkpoint.val.length;rw [ckSize];decide)
    restored
  have package : ∃ weights : Fin JFo_Weights.value.val.length → K,
      decodeKs JFo_Weights.value.val.length
        (slice (bytesOf JFx_NativeBytes.checkpoint.val) 712 (JFo_Weights.value.val.length*16))=some weights ∧
      JFo_Weights.value.val=(List.ofFn weights).map sourceK := ⟨model,readModel,modelEq⟩
  rw [wSize] at package
  obtain ⟨weights,readWeights,weightsEq⟩:=package
  have state : accumulator value=(⟨weights,rhs,power,10⟩ : QueryAccumulator.State K E) :=
    JFo_AccumulatorState.source value weights rhs power weightsEq rhsEq powerEq rfl
  change FoldedLeafCodec.decodeWide (slice (bytesOf JFx_NativeBytes.checkpoint.val) 664 32)=some rhs at readRhs
  change ExactLeafFieldCodec.decodeQM31 (slice (bytesOf JFx_NativeBytes.checkpoint.val) 696 16)=some power at readPower
  rw [decodeAccumulator,if_pos header,readRhs,readPower,readWeights]
  simp only [Option.bind_eq_bind,Option.bind_some]
  rw [state]

#print axioms header
#print axioms source
end AspisR1.JFo_DecodedAccumulator
end
