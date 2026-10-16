import RawCutTypedDecode
import R1CanonicalCutOpeningWordProjection
import RawCutWordsFromView
import R1MixedLeafDecoder

/-! The actual raw-byte commitment-cut maps and their strict Merkle opening
payloads feed the literal opening-word projection. The accepted opening,
log-containment, root parsing and strict payload-decode premises are explicit;
this is not yet a source-verifier refinement theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutOpeningWordProjection

open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.RawCutTypedDecode
open AspisR1.RawByteCutRecovery
open AspisR1.TypedRecoveredWords
open AspisR1.FoldedLeafCodec
open AspisR1.FoldedRecoveredWord
open AspisR1.MixedLeafDecoder
open AspisR1.MerkleIndexGeometry
open AspisR1.CanonicalCutTypedProjection
open AspisR1.CanonicalCutSemanticRead
open AspisR1.CanonicalCutOpeningWordProjection
open AspisR1.LiteralOpeningView
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Compose the three accepted actual byte-log Merkle openings with the raw
cut recovery maps, then project their decoded slots through the literal
opening reader's commitment-time word. `wordsFromRawCuts` is the constructor
used by `RawCutWordsFromView.buildWords`; callers can identify it with the
recorded verifier run using that module's `buildWords_eq_actual_cuts`. -/
theorem actual_raw_cut_openings_project_literal_word
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q)
      emptyTable tr)
    (f0 f2 f30 : Bytes) (r0 r2 r30 : State)
    (hread0 : Read tr f0) (hread2 : Read tr f2) (hread30 : Read tr f30)
    (hpred0 : RawByteCollisionTargets.pred 8 f0 = some r0)
    (hpred2 : RawByteCollisionTargets.pred 8 f2 = some r2)
    (hpred30 : RawByteCollisionTargets.pred 9 f30 = some r30)
    (w : Words)
    (hwords : w = wordsFromRawCuts tr f0 f2 f30 r0 r2 r30)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View)
    (hreadOpening : LiteralOpeningView.read rs = some v)
    (q : Fin 262144)
    (packed1 salt1 : List ExactLeafFieldCodec.Byte)
    (hw1 : packed1.length = 480) (hs1 : salt1.length = 32)
    {slots1 : List (Fin 8)} (path1 : Path slots1)
    (haccept1 : (eval H (MerkleProgram.leafProgram path1
      (leafInput 0x71 packed1 salt1))).2 = r0)
    (hopen1 : ∀ a, Read (eval H (MerkleProgram.leafProgram path1
      (leafInput 0x71 packed1 salt1))).1 a → Read tr a)
    (payload1 : TypedRecoveredWords.C1) (hdecode1 : decodeC1 packed1 = some payload1)
    (packed2 salt2 : List ExactLeafFieldCodec.Byte)
    (hw2 : packed2.length = 128) (hs2 : salt2.length = 32)
    {slots2 : List (Fin 8)} (path2 : Path slots2)
    (haccept2 : (eval H (MerkleProgram.leafProgram path2
      (leafInput 0xf1 packed2 salt2))).2 = r2)
    (hopen2 : ∀ a, Read (eval H (MerkleProgram.leafProgram path2
      (leafInput 0xf1 packed2 salt2))).1 a → Read tr a)
    (payload2 : TypedRecoveredWords.C2) (hdecode2 : decodeC2 packed2 = some payload2)
    (packedF saltF : List ExactLeafFieldCodec.Byte)
    (hwF : packedF.length = 128) (hsF : saltF.length = 32)
    {slotsF : List (Fin 8)} (pathF : Path slotsF)
    (hacceptF : (eval H (MerkleProgram.leafProgram pathF
      (leafInput 0x72 packedF saltF))).2 = r30)
    (hopenF : ∀ a, Read (eval H (MerkleProgram.leafProgram pathF
      (leafInput 0x72 packedF saltF))).1 a → Read tr a)
    (payloadF : FoldedLeafCodec.Folded) (hdecodeF : decodeFolded packedF = some payloadF)
    (hslots1 : slots1 = MerkleIndexGeometry.slots 6
      (queryLeaf (CanonicalCutTypedProjection.queryPosition q)).val)
    (hslots2 : slots2 = MerkleIndexGeometry.slots 6
      (queryLeaf (CanonicalCutTypedProjection.queryPosition q)).val)
    (hslotsF : slotsF = MerkleIndexGeometry.slots 6 (foldedIndex q).val) :
    ∃ v',
      LiteralOpeningView.read
        (CanonicalCutEnrichedTranscript.enrichRounds w rs) = some v' ∧
      v'.semantic.map Prod.snd = v.semantic.map Prod.snd ∧
      (∀ l : Fin 26,
        v'.word ⟨l.val, by have hl := l.isLt; omega⟩
          (CanonicalCutTypedProjection.queryPosition q) =
          ExactBaseProjection.embed
            ((payload1 (querySlot
              (CanonicalCutTypedProjection.queryPosition q))).1 l)) ∧
      v'.word ⟨26, by decide⟩ (CanonicalCutTypedProjection.queryPosition q) =
        LiteralOpeningView.eK ((payload2 (querySlot
          (CanonicalCutTypedProjection.queryPosition q))) ⟨0, by decide⟩) ∧
      v'.word ⟨27, by decide⟩ (CanonicalCutTypedProjection.queryPosition q) =
        LiteralOpeningView.eK ((payload2 (querySlot
          (CanonicalCutTypedProjection.queryPosition q))) ⟨1, by decide⟩) ∧
      v'.word ⟨28, by decide⟩ (CanonicalCutTypedProjection.queryPosition q) =
        LiteralOpeningView.eK ((payload1 (querySlot
          (CanonicalCutTypedProjection.queryPosition q))).2) ∧
      w.final q = payloadF (foldedSlot q) := by
  have hc1 := c1_raw_cut_decode iv H tr Q hcons hQ hout f0 8 hread0 r0 hpred0
    packed1 salt1 hw1 hs1 path1 haccept1 hopen1
    (queryLeaf (CanonicalCutTypedProjection.queryPosition q)) hslots1 payload1 hdecode1
  have hc2 := c2_raw_cut_decode iv H tr Q hcons hQ hout f2 8 hread2 r2 hpred2
    packed2 salt2 hw2 hs2 path2 haccept2 hopen2
    (queryLeaf (CanonicalCutTypedProjection.queryPosition q)) hslots2 payload2 hdecode2
  have hfolded := folded_raw_cut_decode iv H tr Q hcons hQ hout f30 9 hread30 r30 hpred30
    packedF saltF hwF hsF pathF hacceptF hopenF (foldedIndex q) hslotsF payloadF hdecodeF
  have hwordMaps : w = wordsFromMaps (rawC1Map tr f0 r0)
      (rawC2Map tr f2 r2) (rawFoldedMap tr f30 r30) := by
    simpa [CanonicalCutEnrichedTranscript.wordsFromRawCuts] using hwords
  exact opening_read_enriched_projects_cut_maps w rs v
    (rawC1Map tr f0 r0) (rawC2Map tr f2 r2) (rawFoldedMap tr f30 r30)
    q payload1 payload2 payloadF hreadOpening hwordMaps hc1 hc2 hfolded

#print axioms actual_raw_cut_openings_project_literal_word

end AspisR1.RawCutOpeningWordProjection
end
