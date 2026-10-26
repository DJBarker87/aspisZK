import SCF_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCF_Obstruction
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

abbrev z : State := fun _ => 0
def salt : Bytes := List.replicate 32 0
def leaf : Bytes := BinMerkle32Leaf.leafInput 0x71 [] salt

/-- Actual executable binary-leaf recovery is sensitive to deleting a query
before a surviving frame. This is a local countermodel, not a deployed forgery
or a counterexample to the complete frozen3 accepted experiment. -/
theorem deleting_before_cut :
    ([( [],z)] : List (Bytes × State)).Sublist [(leaf,z),([],z)] ∧
    (∀ q ∈ ([(leaf,z),([],z)] : List (Bytes × State)), q.2 = (fun _ : Bytes => z) q.1) ∧
    RawCutRecordedWordsExecutableBin.recoverAtExec 0x71 0
      (BinRawByteCutRecovery.cut [(leaf,z),([],z)] []) [] z = some ([],salt) ∧
    RawCutRecordedWordsExecutableBin.recoverAtExec 0x71 0
      (BinRawByteCutRecovery.cut [([],z)] []) [] z = none := by
  have different : leaf ≠ [] := by simp [leaf,BinMerkle32Leaf.leafInput]
  have cut : BinRawByteCutRecovery.cut [(leaf,z),([],z)] [] = [(leaf,z)] := by
    simp [BinRawByteCutRecovery.cut, FS2.Duplex.firstIdx, different]
  have parsed := BinMerkleLeafCodec.parse_leafInput (0x71 : BinMerkle32Path.Byte)
    [] salt 0 rfl (by simp [salt])
  refine ⟨List.Sublist.cons _ (List.Sublist.refl _), ?_, ?_, rfl⟩
  · intro q member
    simp at member
    rcases member with rfl | rfl <;> rfl
  rw [cut]
  simp only [RawCutRecordedWordsExecutableBin.recoverAtExec,
    BinMerkleLeafRecovery.recover, BinMerkleTable.walk, Option.bind_some,
    BinMerkleRecordedLog.leaves, List.filterMap_cons, List.filterMap_nil, leaf, parsed,
    Option.map_some, BinMerkleLeafRecovery.lookupLeaf, if_pos True.intro]

#print axioms deleting_before_cut
end AspisR1.SCF_Obstruction
end
