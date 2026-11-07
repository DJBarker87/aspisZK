import NMT_345StepLengthGuard
import NMT_345StepPrefixRead
import NMT_345StepPrefixCompare
import NMT_345StepPrefixGuard
import NMT_345StepTagOffset
import NMT_345StepTagRead
import NMT_345StepTagExpected
import NMT_345StepTagGuard
import NMT_345StepSemanticRead
import NMT_345StepProofRange
import NMT_345StepSplitByte
import NMT_345StepSplitCast
import NMT_345ChildStep
import NMT_CallTree
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Complete typed VALUE/CONTROL tail only. Calls remain explicit, so this is
not a physical observation packet or a canonical RowSpec345 root. -/
def tailFold {W : Type} (c : Calls) (s : Bounds W) : Result Ret := do
 if Slice.len s.proofData != s.proofEnd then .ok (.Err .InvalidAccountData) else do
  let proofPrefix ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
    s.proofData { «end» := s.proofStart }
  let mismatch ← c.c0 core.cmp.PartialEqU8 proofPrefix s.candidate
  if mismatch then .ok (.Err .InvalidAccountData) else do
   let offset ← lift (Usize.wrapping_add s.proofStart 8#usize)
   let tag ← Slice.index_usize s.proofData offset
   let expected ← c.c3 NMT_stage1_owned.aspis_r1_cost_probe.transport.Variant.S2
   if tag != expected then .ok (.Err .InvalidAccountData) else do
    let pub ← c.c5 s.statement
    let proof ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      s.proofData {start := s.proofStart, «end» := s.proofEnd}
    let kbyte ← Slice.index_usize s.data 1#usize
    let k ← lift (UScalar.cast .Usize kbyte)
    tryStep (c.c11 pub s.publicData proof k) fun checkpoint =>
      if alloc.vec.Vec.len checkpoint != Slice.len s.checkpointData
      then .ok (.Err .InvalidAccountData) else .ok (.Ok checkpoint)
/-- Fold of previously checked one-occurrence equations. No whole-call-tree
erasure, downstream child evaluation or large concrete normalization. -/
theorem tail_fold {W : Type} (c : Calls) (s : Bounds W) : raw11 c s = tailFold c s := by
 unfold tailFold
 rw [stepLengthGuard]
 split
 · rfl
 · rw [stepPrefixRead]
   apply AspisR1.NMT_CallTree.result_congr
   intro proofPrefix
   rw [stepPrefixCompare]
   apply AspisR1.NMT_CallTree.result_congr
   intro mismatch
   rw [stepPrefixGuard]
   split
   · rfl
   · rw [stepTagOffset]
     apply AspisR1.NMT_CallTree.result_congr
     intro offset
     rw [stepTagRead]
     apply AspisR1.NMT_CallTree.result_congr
     intro tag
     rw [stepTagExpected]
     apply AspisR1.NMT_CallTree.result_congr
     intro expected
     rw [stepTagGuard]
     split
     · rfl
     · rw [stepSemanticRead]
       apply AspisR1.NMT_CallTree.result_congr
       intro pub
       rw [stepProofRange]
       apply AspisR1.NMT_CallTree.result_congr
       intro proof
       rw [stepSplitByte]
       apply AspisR1.NMT_CallTree.result_congr
       intro kbyte
       rw [stepSplitCast]
       apply AspisR1.NMT_CallTree.result_congr
       intro k
       rw [stepChild]
       rfl
#print axioms tail_fold
end NMT_345
