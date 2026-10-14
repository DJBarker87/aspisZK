import R1CanonicalPredictedRecovery
import R1CanonicalMerkleCollision

/-! Replace the byte-log collision alternative with the corresponding duplex
collision event, retaining the generic root-predictor and child-target events. -/
set_option autoImplicit false
namespace AspisR1.CanonicalBoundRecovery

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open CanonicalByteHash

variable {M Cv : Type} {L B : Nat}

theorem recover_or_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre : List (Addr L × State))
    (hpre : ∀ q ∈ pre, q.2 = H q.1)
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
      hitsBad (badColl p Qtot) emptyTable
        (pre ++ (eval H (CanonicalMerkleProgram.program path
          (leafInput tag packed salt))).1) ∨
      hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot) emptyTable
        (pre ++ (eval H (CanonicalMerkleProgram.program path
          (leafInput tag packed salt))).1) ∨
      hitsBad (ParsedTargetsCollision.bad pred Qtot) emptyTable
        (pre ++ (eval H (CanonicalMerkleProgram.program path
          (leafInput tag packed salt))).1) := by
  have h := CanonicalPredictedRecovery.recover_or_events Qtot H pre hpre tag width
    packed salt hw hs hleaf hnode path root pred b j hcommit hpred haccept hQ
  rcases h with hrecover | hcollision | hchild | hpredicted
  · exact Or.inl hrecover
  · exact Or.inr (Or.inl (CanonicalMerkleCollision.hits_collision p Qtot H pre
      hpre path (leafInput tag packed salt) hleaf hnode hQ hcollision))
  · exact Or.inr (Or.inr (Or.inl hchild))
  · exact Or.inr (Or.inr (Or.inr hpredicted))

theorem recover_of_no_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre : List (Addr L × State))
    (hpre : ∀ q ∈ pre, q.2 = H q.1)
    (tag : Merkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (hw : packed.length = width) (hs : salt.length = 32)
    (hleaf : (leafInput tag packed salt).length ≤ L) (hnode : 257 ≤ L)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
    (pred : Fin B → Addr L → Option State) (b : Addr L) (j : Fin B)
    (hcommit : Read pre b) (hpred : pred j b = some root)
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput tag packed salt))).2 = root)
    (hQ : firstReads emptyTable (pre ++ (eval H (CanonicalMerkleProgram.program path
      (leafInput tag packed salt))).1) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable
      (pre ++ (eval H (CanonicalMerkleProgram.program path
        (leafInput tag packed salt))).1))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable (pre ++ (eval H (CanonicalMerkleProgram.program path
        (leafInput tag packed salt))).1))
    (hnoPred : ¬ hitsBad (ParsedTargetsCollision.bad pred Qtot) emptyTable
      (pre ++ (eval H (CanonicalMerkleProgram.program path
        (leafInput tag packed salt))).1)) :
    recover (nodes (CanonicalOracleLog.byteLog pre))
        (leaves tag width (CanonicalOracleLog.byteLog pre)) slots root =
        some (packed, salt) := by
  rcases recover_or_events p Qtot H pre hpre tag width packed salt hw hs hleaf hnode
      path root pred b j hcommit hpred haccept hQ with
    hrecover | hcoll | hchild | hroot
  · exact hrecover
  · exact False.elim (hnoColl hcoll)
  · exact False.elim (hnoChild hchild)
  · exact False.elim (hnoPred hroot)

#print axioms recover_or_events
#print axioms recover_of_no_events

end AspisR1.CanonicalBoundRecovery
