import OraclePortAccLogParentSchedules

/-! Place the common frame after the permuted block: the recovery obstruction
persists even when no query crosses the first-frame commitment cut. The empty
frame isolates the actual cut primitive, not a full protocol transcript. -/
set_option autoImplicit false
namespace AspisR1.OraclePortAccLogCuts
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortAccLogPermutation OraclePortAccLogRecoveryLog OraclePortAccLogRecoveryWorld

abbrev levelFramed := levelLog ++ [([],oracle [])]
abbrev recursiveFramed := recursiveLog ++ [([],oracle [])]

theorem level_cut : RawCutRecordedWordsExecutable.cutBeforeExec levelFramed [] = levelLog := by
  simp [RawCutRecordedWordsExecutable.cutBeforeExec,
    RawCutRecordedWordsExecutable.firstIndexExec,levelFramed,levelLog,encodeNodes,level,
    leaf,BinMerkle32Path.nodeInput,BinMerkle32Leaf.leafInput]

theorem recursive_cut : RawCutRecordedWordsExecutable.cutBeforeExec recursiveFramed [] = recursiveLog := by
  simp [RawCutRecordedWordsExecutable.cutBeforeExec,
    RawCutRecordedWordsExecutable.firstIndexExec,recursiveFramed,recursiveLog,encodeNodes,recursive,
    leaf,BinMerkle32Path.nodeInput,BinMerkle32Leaf.leafInput]

theorem same_frame_recovery_obstruction :
    RawCutRecordedWordsExecutable.cutBeforeExec levelFramed [] = levelLog ∧
    RawCutRecordedWordsExecutable.cutBeforeExec recursiveFramed [] = recursiveLog ∧
    RawCutRecordedWordsExecutableBin.recoverAtExec 0x71 0
        (RawCutRecordedWordsExecutable.cutBeforeExec levelFramed []) [0,0,0] (d 13) ≠
      RawCutRecordedWordsExecutableBin.recoverAtExec 0x71 0
        (RawCutRecordedWordsExecutable.cutBeforeExec recursiveFramed []) [0,0,0] (d 13) := by
  refine ⟨level_cut,recursive_cut,?_⟩
  rw [level_cut,recursive_cut,level_log_recovers,recursive_log_recovers]
  simp only [ne_eq,reduceCtorEq,not_false_eq_true]

#print axioms level_cut
#print axioms recursive_cut
#print axioms same_frame_recovery_obstruction
end AspisR1.OraclePortAccLogCuts
