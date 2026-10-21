import OraclePortAccLogRecoveryWorld
import OraclePortInnerOrderFrozen

/-! The seven-record permutation is produced by the actual generic source
level runner versus the actual recursive tree executor, at height three.
Leaves are prehashed to isolate parent scheduling; no full-slot reachability
or height-18 accepted source/model equality is asserted. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortAccLogParentSchedules
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OracleDecisionMultiTree BinMerkleTable BinMerkle32Path OraclePortInnerOrderFrozen
open OraclePortAccLogPermutation OraclePortAccLogRecoveryLog OraclePortAccLogRecoveryWorld
attribute [local instance] Classical.propDecidable

def tree : Tree := .branch
  (.branch (.branch (.supplied (d 0)) (.supplied (d 1)))
           (.branch (.supplied (d 2)) (.supplied (d 3))))
  (.branch (.branch (.supplied (d 4)) (.supplied (d 5)))
           (.branch (.supplied (d 6)) (.supplied (d 7))))

def live : Live := [(0,d 0),(1,d 1),(2,d 2),(3,d 3),(4,d 4),(5,d 5),(6,d 6),(7,d 7)]

theorem source_parent_schedule :
    eval oracle (runLevels 3 live []) = (encodeNodes level,some ([(0,d 13)],[])) := by
  simp [runLevels,runLevel,live,paired,eval_bind,eval,oracle,node_ne_leaf,
    BinMerkleNodeCodec.readChildren_nodeInput,children,d,encodeNodes,level,A,B,C,D,E,F,G]

theorem recursive_parent_schedule :
    eval oracle (OracleDecisionMultiTree.execute tree) = (encodeNodes recursive,d 13) := by
  simp [tree,OracleDecisionMultiTree.execute,eval_bind,eval,oracle,node_ne_leaf,
    BinMerkleNodeCodec.readChildren_nodeInput,children,d,encodeNodes,recursive,A,B,C,D,E,F,G]

/-- Same root and parent-read multiset, but the existing byte-log recovery
primitive is not invariant under exactly these two parent schedules. -/
theorem actual_schedule_recovery_obstruction :
    (eval oracle (runLevels 3 live [])).1 = encodeNodes level ∧
    (eval oracle (OracleDecisionMultiTree.execute tree)).1 = encodeNodes recursive ∧
    BinMerkleRecordedLog.Consistent oracle levelLog ∧
    BinMerkleRecordedLog.Consistent oracle recursiveLog ∧
    RawCutRecordedWordsExecutableBin.recoverAtExec 0x71 0 levelLog [0,0,0] (d 13) = none ∧
    RawCutRecordedWordsExecutableBin.recoverAtExec 0x71 0 recursiveLog [0,0,0] (d 13) =
      some ([],salt) :=
  ⟨congrArg Prod.fst source_parent_schedule,congrArg Prod.fst recursive_parent_schedule,
    level_consistent,recursive_consistent,level_log_recovers,recursive_log_recovers⟩

#print axioms source_parent_schedule
#print axioms recursive_parent_schedule
#print axioms actual_schedule_recovery_obstruction
end AspisR1.OraclePortAccLogParentSchedules
end
