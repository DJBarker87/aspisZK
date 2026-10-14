import R1CanonicalMerkleRecovery
import R1MerkleC1Target

/-! Initial-C1-frame specialization: a prior read of the frame fixes the root
target, so the remaining root-preimage case is covered by its parsed-target
event. This is a literal oracle-program theorem, not Rust correspondence or
an efficient whole-spend extractor. -/
set_option autoImplicit false
namespace AspisR1.CanonicalC1Recovery

open FS FS2.Duplex
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.MemoizedProgramLaw
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open CanonicalByteHash

variable {L : Nat}

theorem recover_or_events (Qtot : Nat) (H : Addr L → State)
    (pre : List (Addr L × State)) (hpre : ∀ q ∈ pre, q.2 = H q.1)
    (pubBytes : Bytes) (hpub : pubBytes.length < 2^32)
    (hframe : 75 + pubBytes.length ≤ L) (hsize : 514 ≤ L)
    (packed salt : Bytes) (hw : packed.length = 480) (hs : salt.length = 32)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
    (hcommit : Read pre (PublicInitFrame.addr pubBytes hframe root))
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput 0x71 packed salt))).2 = root)
    (hQ : firstReads emptyTable (pre ++ (eval H (CanonicalMerkleProgram.program path
      (leafInput 0x71 packed salt))).1) ≤ Qtot) :
    recover (nodes (CanonicalOracleLog.byteLog pre))
        (leaves 0x71 480 (CanonicalOracleLog.byteLog pre)) slots root =
        some (packed, salt) ∨
      CrossTraceCollision (hashBytes H) ((CanonicalOracleLog.byteLog pre).map Prod.fst)
        (fullTrace (hashBytes H) path (leafInput 0x71 packed salt)) ∨
      hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot) emptyTable
        (pre ++ (eval H (CanonicalMerkleProgram.program path
          (leafInput 0x71 packed salt))).1) ∨
      hitsBad (ParsedTargetsCollision.bad (MerkleC1Target.pred pubBytes) Qtot) emptyTable
        (pre ++ (eval H (CanonicalMerkleProgram.program path
          (leafInput 0x71 packed salt))).1) := by
  let leaf := leafInput 0x71 packed salt
  let post := (eval H (CanonicalMerkleProgram.program path leaf)).1
  have hleaf : leaf.length ≤ L := by
    dsimp [leaf, leafInput]
    simp only [List.length_cons, List.length_append, hw, hs]
    omega
  have hnode : 257 ≤ L := by omega
  have hcases := CanonicalMerkleRecovery.recover_or_events Qtot H pre hpre 0x71 480
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
    have hp : MerkleC1Target.pred pubBytes 0
        (PublicInitFrame.addr pubBytes hframe root) = some (H (encode input)) := by
      rw [MerkleC1Target.pred_init pubBytes hpub hframe root]
      exact congrArg some heq.symm
    exact Or.inr (Or.inr (Or.inr
      (ParsedTargetsPrefixHit.prefix_hit (MerkleC1Target.pred pubBytes) Qtot H pre post
        hcons hQ (encode input) (PublicInitFrame.addr pubBytes hframe root)
        hread hnot hcommit 0 hp)))
  · exact Or.inr (Or.inr (Or.inl hchild))

#print axioms recover_or_events

end AspisR1.CanonicalC1Recovery
