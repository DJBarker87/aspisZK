import CanonicalCutEnrichedTranscript
import R1TypedRecoveredWords
import R1FoldedLeafCodec
import R1MerkleIndexGeometry
import RawByteCutRecovery
import RawByteCutStability

/-! Strict leaf decodes obtained from the actual byte-log commitment cut.
The only premises are the accepted opening, its containment in the recorded
log, the raw-address collision exclusion, and the strict payload decode. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutTypedDecode

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.RawByteCutRecovery
open AspisR1.RawByteCutStability
open AspisR1.TypedRecoveredWords
open AspisR1.MixedLeafDecoder
open AspisR1.FoldedLeafCodec
open AspisR1.MerkleIndexGeometry

theorem c1_raw_cut_decode
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q)
      emptyTable tr)
    (frame : Bytes) (j : Fin 11) (hframe : Read tr frame)
    (root : State) (hpred : RawByteCollisionTargets.pred j frame = some root)
    (packed salt : List ExactLeafFieldCodec.Byte)
    (hw : packed.length = 480)
    (hs : salt.length = 32)
    {slots : List (Fin 8)} (path : Path slots)
    (haccept : (eval H (MerkleProgram.leafProgram path
      (leafInput 0x71 packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (MerkleProgram.leafProgram path
      (leafInput 0x71 packed salt))).1 a → Read tr a)
    (leaf : Fin 262144) (hslots : slots = MerkleIndexGeometry.slots 6 leaf.val)
    (payload : TypedRecoveredWords.C1) (hdecode : decodeC1 packed = some payload) :
    TypedRecoveredWords.decodeC1At (rawC1Map tr frame root) leaf = some payload := by
  have hrecover := RawByteCutRecovery.recover_at_first_commitment
    iv H tr Q hcons hQ hout 0x71 480 packed salt hw hs path root frame j
    hframe hpred haccept hopen
  have hrecoverAt : RawByteCutStability.recoverAt 0x71 480
      (RawByteCutRecovery.cut tr frame) slots root = some (packed, salt) := by
    simpa [RawByteCutStability.recoverAt] using hrecover
  have hpacked : rawC1Map tr frame root leaf = some packed := by
    unfold rawC1Map
    rw [← hslots]
    change (RawByteCutStability.recoverAt 0x71 480
      (RawByteCutRecovery.cut tr frame) slots root).map Prod.fst = some packed
    rw [hrecoverAt]
    rfl
  simp [TypedRecoveredWords.decodeC1At, hpacked, hdecode]

theorem c2_raw_cut_decode
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q)
      emptyTable tr)
    (frame : Bytes) (j : Fin 11) (hframe : Read tr frame)
    (root : State) (hpred : RawByteCollisionTargets.pred j frame = some root)
    (packed salt : List ExactLeafFieldCodec.Byte)
    (hw : packed.length = 128)
    (hs : salt.length = 32)
    {slots : List (Fin 8)} (path : Path slots)
    (haccept : (eval H (MerkleProgram.leafProgram path
      (leafInput 0xf1 packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (MerkleProgram.leafProgram path
      (leafInput 0xf1 packed salt))).1 a → Read tr a)
    (leaf : Fin 262144) (hslots : slots = MerkleIndexGeometry.slots 6 leaf.val)
    (payload : TypedRecoveredWords.C2) (hdecode : decodeC2 packed = some payload) :
    TypedRecoveredWords.decodeC2At (rawC2Map tr frame root) leaf = some payload := by
  have hrecover := RawByteCutRecovery.recover_at_first_commitment
    iv H tr Q hcons hQ hout 0xf1 128 packed salt hw hs path root frame j
    hframe hpred haccept hopen
  have hrecoverAt : RawByteCutStability.recoverAt 0xf1 128
      (RawByteCutRecovery.cut tr frame) slots root = some (packed, salt) := by
    simpa [RawByteCutStability.recoverAt] using hrecover
  have hpacked : rawC2Map tr frame root leaf = some packed := by
    unfold rawC2Map
    rw [← hslots]
    change (RawByteCutStability.recoverAt 0xf1 128
      (RawByteCutRecovery.cut tr frame) slots root).map Prod.fst = some packed
    rw [hrecoverAt]
    rfl
  simp [TypedRecoveredWords.decodeC2At, hpacked, hdecode]

theorem folded_raw_cut_decode
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q)
      emptyTable tr)
    (frame : Bytes) (j : Fin 11) (hframe : Read tr frame)
    (root : State) (hpred : RawByteCollisionTargets.pred j frame = some root)
    (packed salt : List ExactLeafFieldCodec.Byte)
    (hw : packed.length = 128)
    (hs : salt.length = 32)
    {slots : List (Fin 8)} (path : Path slots)
    (haccept : (eval H (MerkleProgram.leafProgram path
      (leafInput 0x72 packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (MerkleProgram.leafProgram path
      (leafInput 0x72 packed salt))).1 a → Read tr a)
    (leaf : Fin 65536) (hslots : slots = MerkleIndexGeometry.slots 6 leaf.val)
    (payload : FoldedLeafCodec.Folded) (hdecode : decodeFolded packed = some payload) :
    (rawFoldedMap tr frame root leaf).bind decodeFolded = some payload := by
  have hrecover := RawByteCutRecovery.recover_at_first_commitment
    iv H tr Q hcons hQ hout 0x72 128 packed salt hw hs path root frame j
    hframe hpred haccept hopen
  have hrecoverAt : RawByteCutStability.recoverAt 0x72 128
      (RawByteCutRecovery.cut tr frame) slots root = some (packed, salt) := by
    simpa [RawByteCutStability.recoverAt] using hrecover
  have hpacked : rawFoldedMap tr frame root leaf = some packed := by
    unfold rawFoldedMap
    rw [← hslots]
    change (RawByteCutStability.recoverAt 0x72 128
      (RawByteCutRecovery.cut tr frame) slots root).map Prod.fst = some packed
    rw [hrecoverAt]
    rfl
  simp [hpacked, hdecode]

#print axioms c1_raw_cut_decode
#print axioms c2_raw_cut_decode
#print axioms folded_raw_cut_decode

end AspisR1.RawCutTypedDecode
end
