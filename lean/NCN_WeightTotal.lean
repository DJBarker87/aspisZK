import NCN_ReaderTotal
import CheckpointBytes4Ops
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCN_WeightTotal
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes4Sections

theorem loop_total (old pre suffix : List K) (r : verifier.Reader)
    (size : (pre ++ old ++ suffix).length ≤ Usize.max)
    (bound : r.at.val+16*old.length ≤ r.bytes.val.length) :
    ∃ result, weightLoop CheckpointBytes3Reader.readK old.length r
      ⟨⟨pre ++ old ++ suffix,size⟩,pre.length⟩ = ok result := by
  obtain ⟨result,run⟩ := NCN_ReaderTotal.section_total old.length r bound
  cases result with
  | Err e =>
    exact ⟨.Err e,NCN_WeightErrors.loop_error _ old pre suffix r e size run⟩
  | Ok pair =>
    rcases pair with ⟨xs,last⟩
    obtain ⟨out,done,_,_⟩ := CheckpointBytes4Weights.loop_success
      CheckpointBytes3Reader.readK old pre suffix xs r last size run
    exact ⟨.Ok (out,last),done⟩

theorem weights_total (bytes : Slice U8) (start : Usize) (weights : alloc.vec.Vec K)
    (bound : start.val+16*weights.val.length ≤ bytes.val.length) :
    ∃ result, CheckpointBytes4Ops.readWeights bytes start weights = ok result := by
  have size : (([] : List K) ++ weights.val ++ []).length ≤ Usize.max := by
    simpa only [List.nil_append,List.append_nil] using weights.property
  obtain ⟨result,run⟩ := loop_total weights.val [] [] ⟨bytes,start⟩ size bound
  have step : weightLoop CheckpointBytes3Reader.readK weights.val.length
      ⟨bytes,start⟩ ⟨⟨weights.val,weights.property⟩,0⟩ = ok result := by
    simpa only [List.nil_append,List.append_nil,List.length_nil] using run
  unfold CheckpointBytes4Ops.readWeights CheckpointBytes4Ops.weightsUsing
  rw [step,bind_tc_ok]
  cases result with
  | Err e => exact ⟨.Err e,rfl⟩
  | Ok pair => exact ⟨.Ok (⟨pair.1.slice.val,pair.1.slice.property⟩,pair.2.at),rfl⟩

#print axioms loop_total
#print axioms weights_total
end AspisR1.NCN_WeightTotal
