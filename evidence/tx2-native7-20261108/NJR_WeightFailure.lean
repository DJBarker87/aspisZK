import NJR_ReaderCut
import NJJ_Common
set_option autoImplicit false
noncomputable section
namespace NJR_WeightFailure
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open CheckpointBytes4Sections CheckpointBytes4Weights

/-- Error counterpart of the retained loop_success theorem. Every entered
iteration uses the SAME Reader and actual next/back destination. The first
failed read returns its exact error and no owned Vec. Native drop/backing
observations are separately the corrected NJR_ReaderCut; this theorem does not
invent an allocator event or returned error vector. -/
theorem loop (read : ReadK) (old pre suffix : List K) (r : verifier.Reader)
 (bound : (pre ++ old ++ suffix).length ≤ Usize.max) (error : verifier.Error)
 (failure : readList read old.length r=ok (.Err error)) :
 weightLoop read old.length r ⟨⟨pre ++ old ++ suffix,bound⟩,pre.length⟩=ok (.Err error) := by
 induction old generalizing pre r with
 | nil => cases failure
 | cons y old ih =>
  simp only [List.length_cons,readList] at failure
  obtain ⟨⟨value,next⟩,readRun,tail⟩:=OraclePortCkptAbiTry.bind_success _ _ _ failure
  have slot : pre.length < (pre ++ y::old ++ suffix).length := by
   simp only [List.length_append,List.length_cons];omega
  cases value with
  | Err e =>
   have same : e=error := core.result.Result.Err.inj (Result.ok.inj tail)
   subst e
   simp only [List.length_cons,weightLoop,core.slice.iter.IteratorIterMut.next]
   rw [dif_pos (show pre.length < (Slice.len ⟨pre ++ y::old ++ suffix,bound⟩).val from slot)]
   simp only [bind_tc_ok]
   rw [readRun]
   rfl
  | Ok x =>
   obtain ⟨rest,restRun,tail⟩:=OraclePortCkptAbiTry.bind_success _ _ _ tail
   cases rest with
   | Ok pair => cases tail
   | Err e =>
    have same : e=error := core.result.Result.Err.inj (Result.ok.inj tail)
    subst e
    have newBound : ((pre ++ [x]) ++ old ++ suffix).length ≤ Usize.max := by
     simpa [List.length_append] using bound
    have run:=ih (pre ++ [x]) next newBound restRun
    simp only [List.length_cons,weightLoop,core.slice.iter.IteratorIterMut.next]
    rw [dif_pos (show pre.length < (Slice.len ⟨pre ++ y::old ++ suffix,bound⟩).val from slot)]
    simp only [bind_tc_ok]
    rw [readRun]
    simp only [bind_tc_ok]
    change weightLoop read old.length next
     ⟨Slice.setAtNat (⟨pre ++ y::old ++ suffix,bound⟩ : Slice K) pre.length x,pre.length+1⟩=_
    rw [replace_slot]
    simpa only [List.length_append,List.length_singleton] using run

/-- Instantiate at the actual closed readWeights caller, preserving the exact
error arm of the complete owned Result. No success or output-vector premise. -/
theorem weights (bytes : Slice U8) (start : Usize) (v : alloc.vec.Vec K)
 (error : verifier.Error)
 (failure : readList CheckpointBytes3Reader.readK v.val.length ⟨bytes,start⟩=ok (.Err error)) :
 CheckpointBytes4Ops.readWeights bytes start v=ok (.Err error) := by
 have run:=loop CheckpointBytes3Reader.readK v.val [] [] ⟨bytes,start⟩
  (by simpa only [List.nil_append,List.append_nil] using v.property) error failure
 simp only [List.nil_append,List.append_nil,List.length_nil] at run
 unfold CheckpointBytes4Ops.readWeights CheckpointBytes4Ops.weightsUsing
 rw [run]
 rfl

#print axioms loop
#print axioms weights
end NJR_WeightFailure
