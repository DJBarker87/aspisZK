import BinSourceCommitmentWords
import WireTx2LeafCalls

/-! Frozen stage-2 folded leaf to binary causal-word adapter. The retained
LeafOps interface exposes external private hashing and salt conversion.
Path acceptance/logging and backend interpretation remain named premises. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1Stage2.BinStage2FoldedWord
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1.BinSourceCommitmentWords
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def byte (b : U8) : AspisV8R19.DuplexFrames.Byte := b.bv.toFin
def raw (s : Slice U8) : Bytes := s.val.map byte

theorem leaf_input (values : Slice U8) (salt : WireTx2.Bytes32) :
    (WireTx2.inputBytes (WireTx2.leafParts 114#u8 values salt)).map byte =
      BinMerkle32Leaf.leafInput 0x72 (raw values) (raw (Array.to_slice salt)) := by
  change ([16#u8,114#u8] ++ (values.val ++ (salt.val ++ []))).map byte =
    BinMerkle32Leaf.leafInput 0x72 (raw values) (raw (Array.to_slice salt))
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_nil,
    BinMerkle32Leaf.leafInput, raw, Array.to_slice]
  rfl

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Exact slices of a successful tree-2 call, not independently supplied leaf
bytes. The backend digest equation uses the existing named LeafDigestLaw. -/
theorem folded_leaf_success (ops : LeafOps) (law : WireTx2.LeafDigestLaw ops)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (q : Slice U8) (out : WireTx2.Bytes32)
    (hcall : verifier.candidate.batch_leafWithWireOps ops D hash 2#usize q = ok out) :
    ∃ (values : Slice U8) (salt : WireTx2.Bytes32),
      values.val.length = 128 ∧
      D.digest hash (WireTx2.leafParts 114#u8 values salt) = ok out ∧
      ∃ saltBytes : Slice U8,
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          q { start := 800#usize, «end» := 832#usize } = ok saltBytes ∧
        ops.salt saltBytes = ok salt ∧
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          q { start := 672#usize, «end» := 800#usize } = ok values := by
  unfold verifier.candidate.batch_leafWithWireOps at hcall
  simp only [show (2#usize).val = 2 from rfl] at hcall
  obtain ⟨saltBytes, hs, hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨salt, hc, hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨values, hv, hcall⟩ := bind_success _ _ _ hcall
  have hw := WireTx2.range_width q values 672#usize 800#usize hv
  have h672 : (672#usize).val = 672 := rfl
  have h800 : (800#usize).val = 800 := rfl
  rw [h672,h800] at hw
  exact ⟨values,salt,by omega,(law D hash 114#u8 values salt) ▸ hcall,
    saltBytes,hs,hc,hv⟩

/-- The strict decode of the actual stage-2 folded values projects to the
single word fixed before the commitment read. Quantified acceptance/read
premises expose precisely the R13/R10 joins still owed for this retained body. -/
theorem accepted_folded_projects_word
    (ops : LeafOps) (law : WireTx2.LeafDigestLaw ops)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (q : Slice U8) (out : WireTx2.Bytes32)
    (hcall : verifier.candidate.batch_leafWithWireOps ops D hash 2#usize q = ok out)
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (root : State) (frame : Bytes) (j : Fin 5) (hread : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root)
    (i : Fin 262144)
    (path : BinMerkle32Path.Path (BinMultiproof.slots 18 (MerkleIndexGeometry.foldedIndex i).val))
    (opened : FoldedLeafCodec.Folded)
    (hdecode : ∀ values salt, D.digest hash (WireTx2.leafParts 114#u8 values salt) = ok out →
      FoldedLeafCodec.decodeFolded (raw values) = some opened)
    (haccept : ∀ values salt, D.digest hash (WireTx2.leafParts 114#u8 values salt) = ok out →
      (eval H (BinMerkleProgram.leafProgram path
        (BinMerkle32Leaf.leafInput 0x72 (raw values) (raw (Array.to_slice salt))))).2 = root)
    (hopen : ∀ values salt, D.digest hash (WireTx2.leafParts 114#u8 values salt) = ok out →
      ∀ a, Read (eval H (BinMerkleProgram.leafProgram path
        (BinMerkle32Leaf.leafInput 0x72 (raw values) (raw (Array.to_slice salt))))).1 a → Read tr a) :
    foldedWord tr frame root i = opened (FoldedRecoveredWord.foldedSlot i) := by
  obtain ⟨values,salt,hw,hd,_⟩ := folded_leaf_success ops law D hash q out hcall
  have hv : (raw values).length = 128 := by simpa [raw] using hw
  have hs : (raw (Array.to_slice salt)).length = 32 := by
    simpa [raw,Array.to_slice] using salt.property
  exact folded_opening_projects_word iv H tr Q hcons hQ hout root frame j hread hpred
    i (raw values) (raw (Array.to_slice salt)) hv hs path opened (hdecode values salt hd)
    (haccept values salt hd) (hopen values salt hd)

#print axioms leaf_input
#print axioms bind_success
#print axioms folded_leaf_success
#print axioms accepted_folded_projects_word
end AspisR1Stage2.BinStage2FoldedWord
end
