import R1CanonicalMerkleRecovery

/-! Recover a salted leaf when its root is fixed by one of a finite family
of deterministic address predictors at a prior query. Exact frame instances
and the commitment-time cut are separate inputs to this generic connection. -/
set_option autoImplicit false
namespace AspisR1.CanonicalPredictedRecovery

open FS FS2.Duplex
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.MemoizedProgramLaw
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open CanonicalByteHash

variable {L B : Nat}

theorem recover_or_events (Qtot : Nat) (H : Addr L → State)
    (pre : List (Addr L × State)) (hpre : ∀ q ∈ pre, q.2 = H q.1)
    (tag : Merkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (hw : packed.length = width) (hs : salt.length = 32)
    (hleaf : (leafInput tag packed salt).length ≤ L) (hnode : 257 ≤ L)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
    (pred : Fin B → Addr L → Option State) (b : Addr L) (j : Fin B)
    (hcommit : Read pre b) (hpred : pred j b = some root)
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput tag packed salt))).2 = root)
    (hQ : firstReads emptyTable (pre ++ (eval H (CanonicalMerkleProgram.program path
      (leafInput tag packed salt))).1) ≤ Qtot) :
    recover (nodes (CanonicalOracleLog.byteLog pre))
        (leaves tag width (CanonicalOracleLog.byteLog pre)) slots root =
        some (packed, salt) ∨
      CrossTraceCollision (hashBytes H) ((CanonicalOracleLog.byteLog pre).map Prod.fst)
        (fullTrace (hashBytes H) path (leafInput tag packed salt)) ∨
      hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot) emptyTable
        (pre ++ (eval H (CanonicalMerkleProgram.program path
          (leafInput tag packed salt))).1) ∨
      hitsBad (ParsedTargetsCollision.bad pred Qtot) emptyTable
        (pre ++ (eval H (CanonicalMerkleProgram.program path
          (leafInput tag packed salt))).1) := by
  let leaf := leafInput tag packed salt
  let post := (eval H (CanonicalMerkleProgram.program path leaf)).1
  have hcases := CanonicalMerkleRecovery.recover_or_events Qtot H pre hpre tag width
    packed salt hw hs hleaf hnode path root haccept hQ
  rcases hcases with hrecover | hcollision | hroot | hchild
  · exact Or.inl hrecover
  · exact Or.inr (Or.inl hcollision)
  · rcases hroot with ⟨input, hin, hnot, heq⟩
    have hread : Read post (encode input) :=
      CanonicalMerkleProgram.read_of_input H path leaf hin
    have hcons : ∀ q ∈ pre ++ post, q.2 = H q.1 := by
      intro q hq
      rcases List.mem_append.mp hq with hp | hsuf
      · exact hpre q hp
      · exact FS.eval_consistent H (CanonicalMerkleProgram.program path leaf) q hsuf
    have hp : pred j b = some (H (encode input)) :=
      hpred.trans (congrArg some heq.symm)
    exact Or.inr (Or.inr (Or.inr
      (ParsedTargetsPrefixHit.prefix_hit pred Qtot H pre post
        hcons hQ (encode input) b hread hnot hcommit j hp)))
  · exact Or.inr (Or.inr (Or.inl hchild))

#print axioms recover_or_events

end AspisR1.CanonicalPredictedRecovery
