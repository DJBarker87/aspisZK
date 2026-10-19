import RawSourceC2OpeningRecovery
import CanonicalCutEnrichedTranscript

/-! The actual parsed source C2 root determines one pre-commitment typed word.
The same collision exclusion protects every coordinate and every logged,
accepted strict C2 opening. Actual opening-checker/source logging remains open. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawSourceC2WordBinding
open Aeneas Aeneas.Std Result AspisR1
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open CanonicalCutEnrichedTranscript

private theorem actual_frame_read_target
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (values : SemanticPrefixCodec.Full)
    (hfull : SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre)
    (cs : List (SourceFull25.Call D pre)) (c : SourceFull25.Call D pre)
    (hc : c ∈ cs) (hrow : c.row.val = 2)
    (tr : List (Bytes × State)) (hsource : SourceDigestLog.sourceLog cs ⊆ tr) :
    Read tr (CommitmentRootFrames.c2Frame
      (decodeState c.before.state) (SemanticPayloadView.rootAt2 values)) ∧
    RawByteCollisionTargets.pred 8 (CommitmentRootFrames.c2Frame
      (decodeState c.before.state) (SemanticPayloadView.rootAt2 values)) =
        some (SemanticPayloadView.rootAt2 values) := by
  have hframe := RawSourceC2CommitmentFrame.actual_c2_frame values hfull c hrow
  have hpred := RawSourceC2CommitmentFrame.actual_c2_target values hfull c hrow
  have hmem := hsource (SourceDigestLog.sourceLog_absorb_mem cs c hc)
  refine ⟨List.mem_map.mpr ⟨_,hmem,hframe⟩,?_⟩
  rw [← hframe]
  exact hpred

/-- Both packed-map and entire typed-word equality; one collision event, no
coordinate union and no independently chosen source root/frame. -/
theorem actual_c2_word_stable
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (values : SemanticPrefixCodec.Full)
    (hfull : SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre)
    (cs : List (SourceFull25.Call D pre)) (c : SourceFull25.Call D pre)
    (hc : c ∈ cs) (hrow : c.row.val = 2)
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hsource : SourceDigestLog.sourceLog cs ⊆ tr)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q) emptyTable tr) :
    let root := SemanticPayloadView.rootAt2 values
    let frame := CommitmentRootFrames.c2Frame (decodeState c.before.state) root
    rawC2Map tr frame root = fullC2Map tr root ∧
      TypedRecoveredWords.c2Value (rawC2Map tr frame root) =
        TypedRecoveredWords.c2Value (fullC2Map tr root) := by
  obtain ⟨hread,hpred⟩ := actual_frame_read_target values hfull cs c hc hrow tr hsource
  have hstable := RawByteCutStability.all_paths_stable iv H tr Q hcons hQ hout
    0xf1 128 (SemanticPayloadView.rootAt2 values)
    (CommitmentRootFrames.c2Frame (decodeState c.before.state) (SemanticPayloadView.rootAt2 values))
    8 hread hpred
  have hmap : rawC2Map tr (CommitmentRootFrames.c2Frame (decodeState c.before.state)
      (SemanticPayloadView.rootAt2 values)) (SemanticPayloadView.rootAt2 values) =
      fullC2Map tr (SemanticPayloadView.rootAt2 values) := by
    funext leaf
    unfold rawC2Map fullC2Map
    exact congrArg (fun x => x.map Prod.fst)
      (congrFun hstable (MerkleIndexGeometry.slots 6 leaf.val))
  exact ⟨hmap,congrArg TypedRecoveredWords.c2Value hmap⟩

/-- Every accepted logged strict C2 opening agrees with the same typed word
fixed strictly before the actual C2 commitment-frame read. -/
theorem actual_c2_opening_projects_word
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (values : SemanticPrefixCodec.Full)
    (hfull : SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre)
    (cs : List (SourceFull25.Call D pre)) (c : SourceFull25.Call D pre)
    (hc : c ∈ cs) (hrow : c.row.val = 2)
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hsource : SourceDigestLog.sourceLog cs ⊆ tr)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q) emptyTable tr)
    (i : Fin 1048576) (packed salt : Bytes) (hw : packed.length = 128) (hs : salt.length = 32)
    (path : Path (MerkleIndexGeometry.slots 6 (TypedRecoveredWords.queryLeaf i).val))
    (opened : TypedRecoveredWords.C2)
    (hdecode : MixedLeafDecoder.decodeC2 packed = some opened)
    (haccept : (eval H (MerkleProgram.leafProgram path (leafInput 0xf1 packed salt))).2 =
      SemanticPayloadView.rootAt2 values)
    (hopen : ∀ a, Read (eval H (MerkleProgram.leafProgram path
      (leafInput 0xf1 packed salt))).1 a → Read tr a) :
    let root := SemanticPayloadView.rootAt2 values
    let frame := CommitmentRootFrames.c2Frame (decodeState c.before.state) root
    TypedRecoveredWords.c2Value (rawC2Map tr frame root) i =
      opened (TypedRecoveredWords.querySlot i) := by
  obtain ⟨hread,hpred⟩ := actual_frame_read_target values hfull cs c hc hrow tr hsource
  have hrecover := RawByteCutRecovery.recover_at_first_commitment iv H tr Q hcons hQ hout
    0xf1 128 packed salt hw hs path (SemanticPayloadView.rootAt2 values)
    (CommitmentRootFrames.c2Frame (decodeState c.before.state) (SemanticPayloadView.rootAt2 values))
    8 hread hpred haccept hopen
  have hpacked : rawC2Map tr (CommitmentRootFrames.c2Frame (decodeState c.before.state)
      (SemanticPayloadView.rootAt2 values)) (SemanticPayloadView.rootAt2 values)
      (TypedRecoveredWords.queryLeaf i) = some packed := by
    unfold rawC2Map RawByteCutStability.recoverAt
    rw [hrecover]
    rfl
  have hdecoded : TypedRecoveredWords.decodeC2At
      (rawC2Map tr (CommitmentRootFrames.c2Frame (decodeState c.before.state)
        (SemanticPayloadView.rootAt2 values)) (SemanticPayloadView.rootAt2 values))
      (TypedRecoveredWords.queryLeaf i) = some opened := by
    unfold TypedRecoveredWords.decodeC2At
    rw [hpacked]
    exact hdecode
  simp only [TypedRecoveredWords.c2Value,hdecoded,Option.getD_some]

#print axioms actual_c2_word_stable
#print axioms actual_c2_opening_projects_word
end AspisR1PublicPreparation.RawSourceC2WordBinding
end
