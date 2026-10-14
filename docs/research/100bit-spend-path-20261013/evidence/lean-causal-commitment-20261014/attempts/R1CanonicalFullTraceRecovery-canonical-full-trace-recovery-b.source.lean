import R1CanonicalReadCollision
import R1CanonicalPredictedRecovery

/-! Canonical Merkle recovery against an arbitrary consistent actual trace
containing both the prior reads and the opening-program reads. Intervening
queries remain in the trace and in the first-read bound. -/
set_option autoImplicit false
namespace AspisR1.CanonicalFullTraceRecovery

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open CanonicalByteHash

variable {M Cv : Type} {L B : Nat}

theorem recover_or_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (tag : Merkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (hw : packed.length = width) (hs : salt.length = 32)
    (hleaf : (leafInput tag packed salt).length ≤ L) (hnode : 257 ≤ L)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
    (pred : Fin B → Addr L → Option State) (b : Addr L) (j : Fin B)
    (hcommit : Read pre b) (hpred : pred j b = some root)
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput tag packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (CanonicalMerkleProgram.program path
      (leafInput tag packed salt))).1 a → Read (pre ++ post) a)
    (hQ : firstReads emptyTable (pre ++ post) ≤ Qtot) :
    recover (nodes (CanonicalOracleLog.byteLog pre))
        (leaves tag width (CanonicalOracleLog.byteLog pre)) slots root =
        some (packed, salt) ∨
      hitsBad (badColl p Qtot) emptyTable (pre ++ post) ∨
      hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
        emptyTable (pre ++ post) ∨
      hitsBad (ParsedTargetsCollision.bad pred Qtot) emptyTable (pre ++ post) := by
  have hpre : ∀ q ∈ pre, q.2 = H q.1 := by
    intro q hq
    exact hcons q (List.mem_append.mpr (Or.inl hq))
  have hpostRead : ∀ a,
      Read (eval H (CanonicalMerkleProgram.program path (leafInput tag packed salt))).1 a →
        Read (pre ++ post) a := hopen
  have heval := CanonicalMerkleProgram.eval_program H path (leafInput tag packed salt)
  have haccept' := haccept
  rw [heval] at haccept'
  have hroot : root = foldPath (hashBytes H) path
      (hashBytes H (leafInput tag packed salt)) := haccept'.symm
  have hcases := CanonicalOracleLog.recover_or_bad H pre hpre tag width packed salt
    hw hs path root hroot
  rcases hcases with hrecover | hcollision | habsent
  · exact Or.inl hrecover
  · exact Or.inr (Or.inl (CanonicalReadCollision.hits_collision p Qtot H pre
      (pre ++ post) hcons hQ
      (fun a ha => List.mem_append.mpr (Or.inl ha)) path
      (leafInput tag packed salt) hleaf hnode hpostRead hcollision))
  · rcases habsent with ⟨input, hin, hnot, htarget⟩
    have hinputBound : input.length ≤ L :=
      CanonicalMerkleProgram.fullTrace_bounded (leafInput tag packed salt)
        hleaf hnode path H hin
    have hreadPost : Read
        (eval H (CanonicalMerkleProgram.program path (leafInput tag packed salt))).1
        (CanonicalByteHash.encode input) :=
      CanonicalMerkleProgram.read_of_input H path (leafInput tag packed salt) hin
    have hreadFull : Read (pre ++ post) (CanonicalByteHash.encode input) :=
      hopen _ hreadPost
    have hnotRead : ¬ Read pre (CanonicalByteHash.encode input) :=
      CanonicalOracleLog.absent_encoded_not_read pre input hinputBound hnot
    have hreadActualPost : Read post (CanonicalByteHash.encode input) := by
      change CanonicalByteHash.encode input ∈ (pre ++ post).map Prod.fst at hreadFull
      rw [List.map_append, List.mem_append] at hreadFull
      rcases hreadFull with hreadPre | hreadPost
      · exact False.elim (hnotRead hreadPre)
      · exact hreadPost
    rcases CanonicalOracleLog.target_cases pre root (hashBytes H input) htarget with
      htargetRoot | ⟨targetAddr, htargetRead, childSlot, hchildPred⟩
    · have hpredAt : pred j b = some (H (CanonicalByteHash.encode input)) := by
        rw [← htargetRoot] at hpred
        simpa [CanonicalByteHash.hashBytes] using hpred
      exact Or.inr (Or.inr (Or.inr
        (ParsedTargetsPrefixHit.prefix_hit pred Qtot H pre post hcons hQ
          (CanonicalByteHash.encode input) b hreadActualPost hnotRead hcommit j hpredAt)))
    · have hchildAt : MerkleChildTargets.pred childSlot targetAddr =
          some (H (CanonicalByteHash.encode input)) := by
        simpa [CanonicalByteHash.hashBytes] using hchildPred
      exact Or.inr (Or.inr (Or.inl
        (ParsedTargetsPrefixHit.prefix_hit MerkleChildTargets.pred Qtot H pre post
          hcons hQ (CanonicalByteHash.encode input) targetAddr hreadActualPost hnotRead
          htargetRead childSlot hchildAt)))

theorem recover_of_no_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (tag : Merkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (hw : packed.length = width) (hs : salt.length = 32)
    (hleaf : (leafInput tag packed salt).length ≤ L) (hnode : 257 ≤ L)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
    (pred : Fin B → Addr L → Option State) (b : Addr L) (j : Fin B)
    (hcommit : Read pre b) (hpred : pred j b = some root)
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput tag packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (CanonicalMerkleProgram.program path
      (leafInput tag packed salt))).1 a → Read (pre ++ post) a)
    (hQ : firstReads emptyTable (pre ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable (pre ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable (pre ++ post))
    (hnoPred : ¬ hitsBad (ParsedTargetsCollision.bad pred Qtot) emptyTable
      (pre ++ post)) :
    recover (nodes (CanonicalOracleLog.byteLog pre))
        (leaves tag width (CanonicalOracleLog.byteLog pre)) slots root =
        some (packed, salt) := by
  rcases recover_or_events p Qtot H pre post hcons tag width packed salt hw hs
      hleaf hnode path root pred b j hcommit hpred haccept hopen hQ with
    hrecover | hcoll | hchild | hpredicted
  · exact hrecover
  · exact False.elim (hnoColl hcoll)
  · exact False.elim (hnoChild hchild)
  · exact False.elim (hnoPred hpredicted)

#print axioms recover_or_events
#print axioms recover_of_no_events

end AspisR1.CanonicalFullTraceRecovery
