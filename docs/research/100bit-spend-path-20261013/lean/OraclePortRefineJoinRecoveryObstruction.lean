import OraclePortRefineJoinCore
import RawCutRecordedWordsExecutableBin

/-! A countermodel to black-box extraction transport from accepted-log
submultisets. This uses the actual binary leaf-recovery primitive, not a
replacement extractor. It is not an accepted full-dV/frozen-proof witness. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRefineJoinRecoveryObstruction
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortRefineJoin

abbrev z : State := fun _ => 0
abbrev H : Bytes → State := fun _ => z

def salt : Bytes := List.replicate 32 0
def leaf : Bytes := BinMerkle32Leaf.leafInput 0x71 [] salt

def sparse : Verifier := fun _ => .done true
def rich : Verifier := fun _ => .ask leaf fun _ => .done true

theorem sparse_refines_rich : AcceptedRefinement sparse rich := by
  intro oracle i _
  exact ⟨rfl, List.nil_subperm⟩

theorem rich_recovers :
    RawCutRecordedWordsExecutableBin.recoverAtExec 0x71 0 [(leaf,z)] [] z =
      some ([],salt) := by
  have hp := BinMerkleLeafCodec.parse_leafInput (0x71 : BinMerkle32Path.Byte)
    [] salt 0 rfl (by simp [salt])
  simp only [RawCutRecordedWordsExecutableBin.recoverAtExec,
    BinMerkleLeafRecovery.recover,BinMerkleTable.walk,Option.bind_some,
    BinMerkleRecordedLog.leaves,List.filterMap_cons,List.filterMap_nil,leaf,hp,
    Option.map_some,BinMerkleLeafRecovery.lookupLeaf,if_pos True.intro]

theorem sparse_does_not_recover :
    RawCutRecordedWordsExecutableBin.recoverAtExec 0x71 0 [] [] z = none := rfl

/-- Acceptance and the proposed direction of read containment hold, but
successful actual leaf recovery on the model does not transfer to source. -/
theorem recovery_transfer_counterexample :
    AcceptedRefinement sparse rich ∧
    RawCutRecordedWordsExecutableBin.recoverAtExec 0x71 0 [(leaf,z)] [] z ≠ none ∧
    RawCutRecordedWordsExecutableBin.recoverAtExec 0x71 0 [] [] z = none := by
  exact ⟨sparse_refines_rich, by rw [rich_recovers]; simp,
    sparse_does_not_recover⟩

/-- Even equal full multisets do not preserve causal cuts: both queries have
consistent answers in the same oracle world, but straddle the frame. -/
theorem cut_permutation_counterexample :
    ([(leaf,z),([],z)] : List (Bytes × State)).Perm [([],z),(leaf,z)] ∧
    RawCutRecordedWordsExecutable.cutBeforeExec [(leaf,z),([],z)] [] = [(leaf,z)] ∧
    RawCutRecordedWordsExecutable.cutBeforeExec [([],z),(leaf,z)] [] = [] := by
  refine ⟨List.Perm.swap _ _ [], ?_, rfl⟩
  have ne : leaf ≠ [] := by simp [leaf,BinMerkle32Leaf.leafInput]
  simp [RawCutRecordedWordsExecutable.cutBeforeExec,
    RawCutRecordedWordsExecutable.firstIndexExec,ne]

#print axioms sparse_refines_rich
#print axioms rich_recovers
#print axioms sparse_does_not_recover
#print axioms recovery_transfer_counterexample
#print axioms cut_permutation_counterexample
end AspisR1.OraclePortRefineJoinRecoveryObstruction
end
