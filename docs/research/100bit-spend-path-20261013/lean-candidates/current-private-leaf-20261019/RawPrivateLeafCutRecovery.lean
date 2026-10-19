import RawPrivateLeafAcceptedPath
import RawByteCutStability

/-! Actual leaf/path source success discharges the ideal opening and read
premises of the existing commitment-cut recovery theorem. Complete caller
log inclusion, collision exclusion, query budget and frame target are explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PrivateLeaf.RawPrivateLeafCutRecovery
open Aeneas Aeneas.Std Result
open AspisR1
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawPrivateLeafCall RawPrivateLeafAcceptedPath
open AspisR1MerklePathChildren.RawMerkleParentBytes (decodeByte decodeDigest)
open AspisR1MerklePathChildren.RawMerkleAcceptedLiteralPath (ParentCall positions)
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog

theorem accepted_private_leaf_recovered_before_frame {Hash : Type}
    (DL : Digest32 Hash) (DM : AspisR1MerklePathChildren.Digest32 Hash) (hash : Hash)
    (tag : U8) (value : Slice U8) (salt node root : RawPrivateLeafCall.Digest)
    (index : Usize) (path : Slice U8) (width : Nat)
    (hw : (value.val.map decodeByte).length = width)
    (hleaf : state_only_private_merkle.private_leaf_hash_with_digest DL hash tag value salt = ok node)
    (hpath : AspisR1MerklePathChildren.verifier.merkle_path DM hash root index node path = ok true)
    (iv : State) (oracle : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = oracle q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q) emptyTable tr)
    (frame : Bytes) (j : Fin 11) (hframe : Read tr frame)
    (hpred : RawByteCollisionTargets.pred j frame = some (decodeDigest root)) :
    ∃ (calls : List (ParentCall DM hash)) (slots : List (Fin 8)),
      calls.length = 6 ∧ slots.map Fin.val = positions index.val 6 ∧
      ((∀ q ∈ fullRawLog tag value salt node calls, q ∈ tr) →
        RawByteCutStability.recoverAt (decodeByte tag) width
          (RawByteCutRecovery.cut tr frame) slots (decodeDigest root) =
          some (value.val.map decodeByte,salt.val.map decodeByte)) := by
  obtain ⟨calls,slots,p,hcount,hpositions,haccepted⟩ :=
    accepted_private_leaf_path DL DM hash tag value salt node root index path hleaf hpath
  refine ⟨calls,slots,hcount,hpositions,?_⟩
  intro hsub
  obtain ⟨hroot,htrace⟩ := haccepted oracle tr hsub hcons
  have haccept : (eval oracle (MerkleProgram.leafProgram p
      (leafInput (decodeByte tag) (value.val.map decodeByte) (salt.val.map decodeByte)))).2 =
      decodeDigest root := by
    rw [MerkleProgram.eval_leafProgram]
    exact hroot
  have hopen : ∀ a, Read (eval oracle (MerkleProgram.leafProgram p
      (leafInput (decodeByte tag) (value.val.map decodeByte) (salt.val.map decodeByte)))).1 a →
      Read tr a := by
    intro a ha
    rw [MerkleProgram.eval_leafProgram] at ha
    change a ∈ ((fullTrace oracle p (leafInput (decodeByte tag)
      (value.val.map decodeByte) (salt.val.map decodeByte))).map
      (fun input => (input,oracle input))).map Prod.fst at ha
    rw [← htrace] at ha
    obtain ⟨q,hq,heq⟩ := List.mem_map.mp ha
    exact List.mem_map.mpr ⟨q,hsub q hq,heq⟩
  exact RawByteCutRecovery.recover_at_first_commitment iv oracle tr Q hcons hQ hout
    (decodeByte tag) width (value.val.map decodeByte) (salt.val.map decodeByte)
    hw (salt_width salt) p (decodeDigest root) frame j hframe hpred haccept hopen

#print axioms accepted_private_leaf_recovered_before_frame
end AspisR1PrivateLeaf.RawPrivateLeafCutRecovery
end
