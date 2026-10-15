import R1C1TableStability
import R1LaterTableStability
import R1TypedRecoveredWords

/-! Compose the existing first-read table stability results with the total
typed-word projection.  Paths are supplied by the caller; no geometry or
source correspondence is asserted here. -/
set_option autoImplicit false

namespace AspisR1.TypedRecoveryStability

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8PairedCommitment
open AspisR1.CanonicalRecoveryStability
open AspisR1.TypedRecoveredWords

variable {M Cv : Type} {L : Nat}

def packedAt (tag : AspisR1.Merkle32Path.Byte) (width : Nat)
    (tr : List (Addr L × State)) (slots : List (Fin 8)) (root : State) :
    Option (List AspisR1.Merkle32Path.Byte) :=
  (recoverAt tag width tr slots root).map Prod.fst

def c1PackedAt (tr : List (Addr L × State))
    (paths : Fin 262144 → List (Fin 8)) (root : State) :
    Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte) :=
  fun leaf => packedAt 0x71 480 tr (paths leaf) root

def c2PackedAt (tr : List (Addr L × State))
    (paths : Fin 262144 → List (Fin 8)) (root : State) :
    Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte) :=
  fun leaf => packedAt 0xf1 128 tr (paths leaf) root

theorem c1_packed_stable (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (tr represented : List (Addr L × State))
    (pubBytes : Bytes) (hframe : 75 + pubBytes.length ≤ L)
    (root : State) (hsize : 514 ≤ L) (hnode : 257 ≤ L)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable tr)
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable tr)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (hread : Read tr (PublicInitFrame.addr pubBytes hframe root))
    (htable : TraceTable.replay emptyTable represented =
      tableBefore emptyTable tr (PublicInitFrame.addr pubBytes hframe root))
    (paths : Fin 262144 → List (Fin 8)) :
    c1PackedAt represented paths root = c1PackedAt tr paths root := by
  funext leaf
  unfold c1PackedAt packedAt
  exact congrArg (fun o => o.map Prod.fst)
    (congrFun (C1TableStability.c1_table_word_of_read p Qtot H tr represented
      pubBytes hframe root hsize hnode hcons hQ hnoColl hnoChild hnoRoot
      hrepresented hread htable) (paths leaf))

theorem c2_packed_stable (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (tr represented : List (Addr L × State))
    (state : State) (hframe : 71 ≤ L) (root : State)
    (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (hread : Read tr (CommitmentRootFrames.c2Addr state root hframe))
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable tr)
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable tr)
    (htable : TraceTable.replay (emptyTable : Table (Addr L) State) represented =
      tableBefore emptyTable tr (CommitmentRootFrames.c2Addr state root hframe))
    (paths : Fin 262144 → List (Fin 8)) :
    c2PackedAt represented paths root = c2PackedAt tr paths root := by
  funext leaf
  unfold c2PackedAt packedAt
  exact congrArg (fun o => o.map Prod.fst)
    (congrFun (LaterTableStability.c2_table_word_of_read p Qtot H tr represented
      state hframe root hsize hnode hcons hrepresented hread hQ hnoColl hnoChild hnoRoot htable)
      (paths leaf))

theorem typed_word_stable {E : Type} [Field E] (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (tr representedC1 representedC2 : List (Addr L × State))
    (pubBytes : Bytes) (hinitFrame : 75 + pubBytes.length ≤ L)
    (initRoot : State) (hinitSize : 514 ≤ L)
    (c2State : State) (hc2Frame : 71 ≤ L) (c2Root : State) (hc2Size : 162 ≤ L)
    (hnode : 257 ≤ L)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable tr)
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable tr)
    (hrepresentedC1 : ∀ q ∈ representedC1, q.2 = H q.1)
    (hrepresentedC2 : ∀ q ∈ representedC2, q.2 = H q.1)
    (hinitRead : Read tr (PublicInitFrame.addr pubBytes hinitFrame initRoot))
    (hc2Read : Read tr (CommitmentRootFrames.c2Addr c2State c2Root hc2Frame))
    (hinitTable : TraceTable.replay emptyTable representedC1 =
      tableBefore emptyTable tr (PublicInitFrame.addr pubBytes hinitFrame initRoot))
    (hc2Table : TraceTable.replay (emptyTable : Table (Addr L) State) representedC2 =
      tableBefore emptyTable tr (CommitmentRootFrames.c2Addr c2State c2Root hc2Frame))
    (paths : Fin 262144 → List (Fin 8))
    (eM : AspisR1.ExactLeafFieldCodec.M31Exact →+* E)
    (eK : AspisR1.ExactLeafFieldCodec.QM31Exact →+* E) :
    TypedRecoveredWords.word eM eK
      (c1PackedAt representedC1 paths initRoot) (c2PackedAt representedC2 paths c2Root) =
    TypedRecoveredWords.word eM eK
      (c1PackedAt tr paths initRoot) (c2PackedAt tr paths c2Root) := by
  rw [c1_packed_stable p Qtot H tr representedC1 pubBytes hinitFrame initRoot
    hinitSize hnode hcons hQ hnoColl hnoChild hnoRoot hrepresentedC1 hinitRead hinitTable paths]
  rw [c2_packed_stable p Qtot H tr representedC2 c2State hc2Frame c2Root
    hc2Size hnode hcons hrepresentedC2 hc2Read hQ hnoColl hnoChild hnoRoot hc2Table paths]

theorem word_typed_full {E : Type} [Field E]
    (tr : List (Addr L × State)) (paths : Fin 262144 → List (Fin 8))
    (initRoot c2Root : State)
    (eM : AspisR1.ExactLeafFieldCodec.M31Exact →+* E)
    (eK : AspisR1.ExactLeafFieldCodec.QM31Exact →+* E) :
    AspisR1.CandidateDescent.WordTyped
      (TypedRecoveredWords.laneSubfield eM eK)
      (TypedRecoveredWords.word eM eK
        (c1PackedAt tr paths initRoot) (c2PackedAt tr paths c2Root)) :=
  TypedRecoveredWords.word_typed eM eK _ _

#print axioms c1_packed_stable
#print axioms c2_packed_stable
#print axioms typed_word_stable
#print axioms word_typed_full

end AspisR1.TypedRecoveryStability
