import R1CanonicalFullTraceRecovery
import R1RecordedRecoveryWitness
import R1MerkleLogExtension

/-! Later canonical query records cannot create a newly recoverable leaf for
a root already named in the prefix, outside the explicit full-trace events.
This is a causal trace statement, not an arbitrary-table D2 premise. -/
set_option autoImplicit false
namespace AspisR1.CanonicalRecoveryStability

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open CanonicalByteHash

variable {M Cv : Type} {L B : Nat}

def recoverAt (tag : Merkle32Path.Byte) (width : Nat)
    (tr : List (Addr L × State)) (slots : List (Fin 8)) (root : State) :
    Option LeafData :=
  recover (nodes (CanonicalOracleLog.byteLog tr))
    (leaves tag width (CanonicalOracleLog.byteLog tr)) slots root

theorem later_of_earlier (tag : Merkle32Path.Byte) (width : Nat)
    (pre post : List (Addr L × State)) (slots : List (Fin 8)) (root : State)
    (data : LeafData) (h : recoverAt tag width pre slots root = some data) :
    recoverAt tag width (pre ++ post) slots root = some data := by
  unfold recoverAt at h ⊢
  rw [MerkleLogExtension.canonical_byteLog_append,
    MerkleLogExtension.nodes_append, MerkleLogExtension.leaves_append]
  exact MerkleLogExtension.recover_append _ _ _ _ slots root data h

theorem earlier_of_later (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (tag : Merkle32Path.Byte) (width : Nat)
    (hsize : width + 34 ≤ L) (hnode : 257 ≤ L)
    (slots : List (Fin 8)) (root : State)
    (pred : Fin B → Addr L → Option State) (b : Addr L) (j : Fin B)
    (hcommit : Read pre b) (hpred : pred j b = some root)
    (hQ : firstReads emptyTable (pre ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable (pre ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable (pre ++ post))
    (hnoPred : ¬ hitsBad (ParsedTargetsCollision.bad pred Qtot) emptyTable (pre ++ post))
    (packed salt : Bytes)
    (hrec : recoverAt tag width (pre ++ post) slots root = some (packed, salt)) :
    recoverAt tag width pre slots root = some (packed, salt) := by
  obtain ⟨hw, hs, path, hroot, hinputs⟩ :=
    RecordedRecoveryWitness.recover_witness (hashBytes H)
      (CanonicalOracleLog.byteLog (pre ++ post))
      (CanonicalOracleLog.consistent H (pre ++ post) hcons)
      tag width slots root packed salt hrec
  have hleaf : (leafInput tag packed salt).length ≤ L := by
    rw [leaf_input_length tag packed salt hs, hw]
    exact hsize
  have haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput tag packed salt))).2 = root := by
    rw [CanonicalMerkleProgram.eval_program]
    exact hroot
  have hopen : ∀ a, Read (eval H (CanonicalMerkleProgram.program path
      (leafInput tag packed salt))).1 a → Read (pre ++ post) a := by
    intro a ha
    rw [CanonicalMerkleProgram.eval_program] at ha
    change a ∈ ((fullTrace (hashBytes H) path (leafInput tag packed salt)).map
      (fun input => (encode input, hashBytes H input))).map Prod.fst at ha
    rw [List.map_map] at ha
    obtain ⟨input, hin, heq⟩ := List.mem_map.mp ha
    have hr : Read (pre ++ post) (encode input) :=
      CanonicalLogInputs.input_read (hinputs input hin)
    exact heq ▸ hr
  exact CanonicalFullTraceRecovery.recover_of_no_events p Qtot H pre post hcons
    tag width packed salt hw hs hleaf hnode path root pred b j hcommit hpred
    haccept hopen hQ hnoColl hnoChild hnoPred

theorem recover_stable (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (tag : Merkle32Path.Byte) (width : Nat)
    (hsize : width + 34 ≤ L) (hnode : 257 ≤ L)
    (slots : List (Fin 8)) (root : State)
    (pred : Fin B → Addr L → Option State) (b : Addr L) (j : Fin B)
    (hcommit : Read pre b) (hpred : pred j b = some root)
    (hQ : firstReads emptyTable (pre ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable (pre ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable (pre ++ post))
    (hnoPred : ¬ hitsBad (ParsedTargetsCollision.bad pred Qtot) emptyTable (pre ++ post)) :
    recoverAt tag width pre slots root = recoverAt tag width (pre ++ post) slots root := by
  cases hbefore : recoverAt tag width pre slots root with
  | some data =>
      exact (later_of_earlier tag width pre post slots root data hbefore).symm
  | none =>
      cases hafter : recoverAt tag width (pre ++ post) slots root with
      | none => rfl
      | some data =>
          obtain ⟨packed, salt⟩ := data
          have h := earlier_of_later p Qtot H pre post hcons tag width hsize hnode
            slots root pred b j hcommit hpred hQ hnoColl hnoChild hnoPred
            packed salt hafter
          rw [hbefore] at h
          cases h

#print axioms later_of_earlier
#print axioms earlier_of_later
#print axioms recover_stable

end AspisR1.CanonicalRecoveryStability
