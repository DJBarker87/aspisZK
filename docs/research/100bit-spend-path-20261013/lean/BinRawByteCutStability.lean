import BinRawByteCutRecovery
import BinRecordedRecoveryWitness
import BinMerkleLogExtension

/-! All recovered Merkle leaves are already fixed at the first commitment
read. This is simultaneous for every path: the same single collision event
protects the whole recovered word, with no union over its coordinates.
The proof reuses the old recorded-recovery witness and append-stability
lemmas, now on unrestricted literal-byte oracle traces. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.BinRawByteCutStability

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open BinMerkle32Path BinMerkle32Leaf BinMerkleTable BinMerkleLeafRecovery BinMerkleRecordedLog
open BinRawByteCutRecovery

def recoverAt (tag : BinMerkle32Path.Byte) (width : Nat) (log : Log)
    (slots : List (Fin 2)) (root : State) : Option LeafData :=
  recover (nodes log) (leaves tag width log) slots root

theorem later_of_cut (tag : BinMerkle32Path.Byte) (width : Nat)
    (tr : List (Bytes × State)) (frame : Bytes) (slots : List (Fin 2))
    (root : State) (data : LeafData)
    (h : recoverAt tag width (cut tr frame) slots root = some data) :
    recoverAt tag width tr slots root = some data := by
  have hsplit : cut tr frame ++ tr.drop (firstIdx frame tr) = tr :=
    List.take_append_drop _ _
  rw [← hsplit]
  unfold recoverAt at h ⊢
  rw [BinMerkleLogExtension.nodes_append, BinMerkleLogExtension.leaves_append]
  exact BinMerkleLogExtension.recover_append _ _ _ _ slots root data h

theorem cut_of_later (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    (tag : BinMerkle32Path.Byte) (width : Nat) (slots : List (Fin 2)) (root : State)
    (frame : Bytes) (j : Fin 5) (hframe : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root)
    (packed salt : Bytes)
    (hrec : recoverAt tag width tr slots root = some (packed, salt)) :
    recoverAt tag width (cut tr frame) slots root = some (packed, salt) := by
  have hlog : BinMerkleRecordedLog.Consistent H tr := by
    intro input output hin
    exact (hcons (input, output) hin).symm
  obtain ⟨hw, hs, path, hroot, hinputs⟩ :=
    BinRecordedRecoveryWitness.recover_witness H tr hlog tag width slots root
      packed salt hrec
  have haccept : (eval H (BinMerkleProgram.leafProgram path
      (leafInput tag packed salt))).2 = root := by
    rw [BinMerkleProgram.eval_leafProgram]
    exact hroot
  have hopen : ∀ a, Read (eval H (BinMerkleProgram.leafProgram path
      (leafInput tag packed salt))).1 a → Read tr a := by
    intro a ha
    rw [BinMerkleProgram.eval_leafProgram] at ha
    change a ∈ ((fullTrace H path (leafInput tag packed salt)).map
      (fun input => (input, H input))).map Prod.fst at ha
    have hi : a ∈ fullTrace H path (leafInput tag packed salt) := by
      rcases List.mem_map.mp ha with ⟨b, hb, hba⟩
      rcases List.mem_map.mp hb with ⟨input, hinput, hpair⟩
      have hinputA : input = a := (congrArg Prod.fst hpair).trans hba
      exact hinputA ▸ hinput
    exact hinputs a hi
  exact recover_at_first_commitment iv H tr Q hcons hQ hout tag width packed salt
    hw hs path root frame j hframe hpred haccept hopen

theorem recover_stable (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    (tag : BinMerkle32Path.Byte) (width : Nat) (slots : List (Fin 2)) (root : State)
    (frame : Bytes) (j : Fin 5) (hframe : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root) :
    recoverAt tag width (cut tr frame) slots root = recoverAt tag width tr slots root := by
  cases hbefore : recoverAt tag width (cut tr frame) slots root with
  | some data =>
      exact (later_of_cut tag width tr frame slots root data hbefore).symm
  | none =>
      cases hafter : recoverAt tag width tr slots root with
      | none => rfl
      | some data =>
          obtain ⟨packed, salt⟩ := data
          have h := cut_of_later iv H tr Q hcons hQ hout tag width slots root
            frame j hframe hpred packed salt hafter
          rw [hbefore] at h
          cases h

/-- One no-event condition fixes all paths together, including unrecoverable
paths, whose Option values remain `none` in the full log. -/
theorem all_paths_stable (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    (tag : BinMerkle32Path.Byte) (width : Nat) (root : State)
    (frame : Bytes) (j : Fin 5) (hframe : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root) :
    (fun slots => recoverAt tag width (cut tr frame) slots root) =
      (fun slots => recoverAt tag width tr slots root) := by
  funext slots
  exact recover_stable iv H tr Q hcons hQ hout tag width slots root frame j hframe hpred

#print axioms later_of_cut
#print axioms cut_of_later
#print axioms recover_stable
#print axioms all_paths_stable
end AspisR1.BinRawByteCutStability
end
