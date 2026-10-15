import R1CanonicalTypedOpening
import R1RecoveredC2Semantic

/-! Connect the existing accepted C2 opening theorem to the two coordinates
of the recovered semantic pair. This adds no source or protocol claim. -/
set_option autoImplicit false

namespace AspisR1.CanonicalC2SemanticOpening

open AspisR1.CanonicalTypedOpening
open AspisR1.RecoveredC2Semantic
open AspisR1.TypedRecoveredWords
open AspisR1.TypedRecoveryStability
open AspisR1.MixedLeafDecoder
open AspisR1.MerkleIndexGeometry
open AspisR1.Merkle32Path
open AspisR1.Merkle32Leaf
open AspisR1.ExactLeafFieldCodec
open AspisV8R19.DuplexFrames
open FS FS2.Duplex
open AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

variable {M Cv : Type} {L : Nat}
variable {E : Type} [Field E]

theorem c2_pair_at_of_no_events
    (eK : QM31Exact →+* E) (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (state : State) (hframe : 71 ≤ L) (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (packed salt : List AspisR1.ExactLeafFieldCodec.Byte)
    (hw : packed.length = 128) (hs : salt.length = 32)
    (leaf : Fin 262144)
    (path : Path (MerkleIndexGeometry.slots 6 leaf.val)) (root : State)
    (hcommit : Read pre (CommitmentRootFrames.c2Addr state root hframe))
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput 0xf1 packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (CanonicalMerkleProgram.program path
      (leafInput 0xf1 packed salt))).1 a → Read (pre ++ post) a)
    (hQ : firstReads emptyTable (pre ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable (pre ++ post))
    (hnoChild : ¬ hitsBad
      (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot) emptyTable (pre ++ post))
    (hnoRoot : ¬ hitsBad
      (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot) emptyTable (pre ++ post))
    (payload : C2) (hdecode : decodeC2 packed = some payload)
    (i : Fin 1048576) (hindex : queryLeaf i = leaf) :
    (pairAt eK (pre ++ post) root).1 i =
        eK ((payload (querySlot i)) ⟨0, by decide⟩) ∧
      (pairAt eK (pre ++ post) root).2 i =
        eK ((payload (querySlot i)) ⟨1, by decide⟩) := by
  have hopening := CanonicalTypedOpening.c2_decode_of_no_events p Qtot H pre post
    hcons state hframe hsize hnode packed salt hw hs leaf path root hcommit
    haccept hopen hQ hnoColl hnoChild hnoRoot payload hdecode
  have hdecoded : decodeC2At
      (TypedRecoveryStability.c2PackedAt (pre ++ post) paths6C2 root)
      (queryLeaf i) = some payload := by
    rw [hindex]
    have hpaths : paths6C2 = CanonicalTypedOpening.paths6C1C2 := by
      funext x
      rfl
    rw [hpaths]
    exact hopening
  exact ⟨pairAt_fst_of_decode eK (pre ++ post) root i payload hdecoded,
    pairAt_snd_of_decode eK (pre ++ post) root i payload hdecoded⟩

#print axioms c2_pair_at_of_no_events

end AspisR1.CanonicalC2SemanticOpening
