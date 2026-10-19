import BinCanonicalCutWords

/-! Causal typed opening recovery, simultaneously for all coordinates.
Mirrors ThreeCommitmentRecovery.lean:18,51,84 and CanonicalTypedOpening.lean:
38,74,109 via one tag/width/decoder-parametric theorem. This uses raw byte
logs and the single five-target event, not the old bounded-address events. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.BinThreeCommitmentTypedOpening
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open BinMerkle32Path BinMerkle32Leaf

/-- Includes salts and exact leaf widths; the typed decoder may reject.
All three actual decoder functions can be instantiated without new axioms. -/
theorem typed_opening_at_cut {A : Type}
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    (tag : Byte) (width : Nat) (packed salt : Bytes)
    (hw : packed.length = width) (hs : salt.length = 32)
    {ss : List (Fin 2)} (path : Path ss) (root : State)
    (frame : Bytes) (j : Fin 5) (hframe : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root)
    (haccept : (eval H (BinMerkleProgram.leafProgram path
      (leafInput tag packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (BinMerkleProgram.leafProgram path
      (leafInput tag packed salt))).1 a → Read tr a)
    (decode : Bytes → Option A) (value : A) (hd : decode packed = some value) :
    ((BinRawByteCutStability.recoverAt tag width
      (BinRawByteCutRecovery.cut tr frame) ss root).map Prod.fst).bind decode =
      some value := by
  have hr := BinRawByteCutRecovery.recover_at_first_commitment iv H tr Q hcons hQ hout
    tag width packed salt hw hs path root frame j hframe hpred haccept hopen
  change ((BinMerkleLeafRecovery.recover
    (BinMerkleRecordedLog.nodes (BinRawByteCutRecovery.cut tr frame))
    (BinMerkleRecordedLog.leaves tag width (BinRawByteCutRecovery.cut tr frame))
    ss root).map Prod.fst).bind decode = some value
  rw [hr]
  exact hd

/-- The same event fixes the entire typed word, including the decoder's
failure results. There is no union over indices or over decoded lanes. -/
theorem typed_word_stable {I A : Type}
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    (tag : Byte) (width : Nat) (root : State) (frame : Bytes) (j : Fin 5)
    (hframe : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root)
    (paths : I → List (Fin 2)) (decode : Bytes → Option A) :
    (fun i => ((BinRawByteCutStability.recoverAt tag width
      (BinRawByteCutRecovery.cut tr frame) (paths i) root).map Prod.fst).bind decode) =
    (fun i => ((BinRawByteCutStability.recoverAt tag width tr
      (paths i) root).map Prod.fst).bind decode) := by
  have h := BinRawByteCutStability.all_paths_stable iv H tr Q hcons hQ hout
    tag width root frame j hframe hpred
  funext i
  rw [congrFun h (paths i)]

#print axioms typed_opening_at_cut
#print axioms typed_word_stable
end AspisR1.BinThreeCommitmentTypedOpening
end
