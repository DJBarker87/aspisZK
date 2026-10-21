import OraclePortAccLogRecoveryLog

/-! The byte-log permutation counterexample is consistent with ONE total
oracle world. The collision is intentional, not inconsistent answers. -/
set_option autoImplicit false
namespace AspisR1.OraclePortAccLogRecoveryWorld
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree BinMerkleTable BinMerkle32Path
open OraclePortAccLogPermutation OraclePortAccLogRecoveryLog

theorem node_ne_leaf (cs : Children) : nodeInput cs ≠ leaf := by
  intro eq
  have first := congrArg List.head? eq
  change some (0x12 : AspisV8R19.DuplexFrames.Byte) = some 0x10 at first
  contradiction

def oracle (input : Bytes) : State :=
  if input = leaf then d 0 else
    let cs := BinMerkleNodeCodec.readChildren input
    if cs 0 0 = 0 then d 8 else
    if cs 0 0 = 2 then d 9 else
    if cs 0 0 = 4 then d 10 else
    if cs 0 0 = 6 then d 11 else
    if cs 0 0 = 8 then d 10 else
    if cs 1 0 = 11 then d 12 else d 13

theorem leaf_answer : oracle leaf = d 0 := by simp [oracle]

theorem node_answers (entry : Children × State) (he : entry ∈ recursive) :
    oracle (nodeInput entry.1) = entry.2 := by
  simp only [recursive,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [A,B,C,D,E,F,G,oracle,node_ne_leaf,BinMerkleNodeCodec.readChildren_nodeInput,children,d]

theorem recursive_consistent : BinMerkleRecordedLog.Consistent oracle recursiveLog := by
  intro input digest hin
  rcases List.mem_cons.mp hin with eq | hin
  · rcases Prod.mk.inj eq with ⟨rfl,rfl⟩
    exact leaf_answer
  · obtain ⟨entry,he,eq⟩ := List.mem_map.mp hin
    rcases Prod.mk.inj eq with ⟨rfl,rfl⟩
    exact node_answers entry he

theorem level_consistent : BinMerkleRecordedLog.Consistent oracle levelLog := by
  intro input digest hin
  exact recursive_consistent input digest (equal_log_multisets.subset hin)

theorem consistent_byte_log_counterexample :
    BinMerkleRecordedLog.Consistent oracle levelLog ∧
    BinMerkleRecordedLog.Consistent oracle recursiveLog ∧
    levelLog.Perm recursiveLog ∧
    RawCutRecordedWordsExecutableBin.recoverAtExec 0x71 0 levelLog [0,0,0] (d 13) = none ∧
    RawCutRecordedWordsExecutableBin.recoverAtExec 0x71 0 recursiveLog [0,0,0] (d 13) =
      some ([],salt) :=
  ⟨level_consistent,recursive_consistent,equal_log_multisets,
    level_log_recovers,recursive_log_recovers⟩

#print axioms node_ne_leaf
#print axioms leaf_answer
#print axioms node_answers
#print axioms recursive_consistent
#print axioms level_consistent
#print axioms consistent_byte_log_counterexample
end AspisR1.OraclePortAccLogRecoveryWorld
