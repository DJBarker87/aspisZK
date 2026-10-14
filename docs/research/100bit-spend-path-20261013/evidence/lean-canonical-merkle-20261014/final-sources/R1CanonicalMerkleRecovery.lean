import R1CanonicalOracleLog
import R1CanonicalMerkleProgram
import R1ParsedTargetsPrefixHit

/-! Recovery from a prior canonical-query table for a later literal Merkle
oracle program. The root-preimage and cross-trace collision cases remain
explicit; child-target failure is contained in the existing first-read event. -/
set_option autoImplicit false
namespace AspisR1.CanonicalMerkleRecovery

open FS FS2.Duplex
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.MemoizedProgramLaw
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open CanonicalByteHash

variable {L : Nat}

def RootPreimageHit (H : Addr L → State) (pre : List (Addr L × State))
    (root : State) (inputs : List Bytes) : Prop :=
  ∃ input ∈ inputs, ¬ Read pre (encode input) ∧ hashBytes H input = root

theorem recover_or_events (Qtot : Nat) (H : Addr L → State)
    (pre : List (Addr L × State)) (hpre : ∀ q ∈ pre, q.2 = H q.1)
    (tag : Merkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (hw : packed.length = width) (hs : salt.length = 32)
    (hleaf : (leafInput tag packed salt).length ≤ L) (hnode : 257 ≤ L)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput tag packed salt))).2 = root)
    (hQ : firstReads emptyTable (pre ++ (eval H (CanonicalMerkleProgram.program path
      (leafInput tag packed salt))).1) ≤ Qtot) :
    recover (nodes (CanonicalOracleLog.byteLog pre))
        (leaves tag width (CanonicalOracleLog.byteLog pre)) slots root =
        some (packed, salt) ∨
      CrossTraceCollision (hashBytes H) ((CanonicalOracleLog.byteLog pre).map Prod.fst)
        (fullTrace (hashBytes H) path (leafInput tag packed salt)) ∨
      RootPreimageHit H pre root (fullTrace (hashBytes H) path (leafInput tag packed salt)) ∨
      hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot) emptyTable
        (pre ++ (eval H (CanonicalMerkleProgram.program path
          (leafInput tag packed salt))).1) := by
  let leaf := leafInput tag packed salt
  let post := (eval H (CanonicalMerkleProgram.program path leaf)).1
  have hcons : ∀ q ∈ pre ++ post, q.2 = H q.1 := by
    intro q hq
    rcases List.mem_append.mp hq with hp | hsuf
    · exact hpre q hp
    · exact FS.eval_consistent H (CanonicalMerkleProgram.program path leaf) q hsuf
  have hroot : root = foldPath (hashBytes H) path (hashBytes H leaf) := by
    rw [CanonicalMerkleProgram.eval_program] at haccept
    exact haccept.symm
  have hc := CanonicalOracleLog.recover_or_bad H pre hpre tag width packed salt
    hw hs path root hroot
  rcases hc with hrecover | hcollision | hmissing
  · exact Or.inl hrecover
  · exact Or.inr (Or.inl hcollision)
  · rcases hmissing with ⟨input, hin, habsent, htarget⟩
    have hlen : input.length ≤ L :=
      CanonicalMerkleProgram.fullTrace_bounded leaf hleaf hnode path H hin
    have hread : Read post (encode input) :=
      CanonicalMerkleProgram.read_of_input H path leaf hin
    have hnot : ¬ Read pre (encode input) :=
      CanonicalOracleLog.absent_encoded_not_read pre input hlen habsent
    rcases CanonicalOracleLog.target_cases pre root (hashBytes H input) htarget with
      heq | ⟨b, hb, j, hp⟩
    · exact Or.inr (Or.inr (Or.inl ⟨input, hin, hnot, heq⟩))
    · exact Or.inr (Or.inr (Or.inr
        (ParsedTargetsPrefixHit.prefix_hit MerkleChildTargets.pred Qtot H pre post
          hcons hQ (encode input) b hread hnot hb j hp)))

#print axioms recover_or_events

end AspisR1.CanonicalMerkleRecovery
