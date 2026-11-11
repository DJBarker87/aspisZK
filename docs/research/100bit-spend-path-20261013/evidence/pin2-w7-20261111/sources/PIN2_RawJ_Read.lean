import RPz8_RawJ_VerifyRead
import PIN2_S1SemanticCodeVerifyV1
/-! PIN2 W9 (2026-11-11): twins of the release RawJ_InitRead.frame, RawJ_PublicRead.frame and
RawJ_VerifyRead.frame at the three PIN2 levels: the PIN2 lift `newTranscript` (`init_frame`),
the PIN2 lift `publicTranscript` (`public_frame`), the frozen-carrier `publicTranscriptPIN2`
(`publicPIN2_frame`: one extra `right_read` for the pure copy-back) and `verifyPIN2`
(`verify_frame`).  Each proof is the release tactic script with the PIN2 names; the
conclusions are the release ones (the frame decodes to `decodeState root`). -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PIN2_RawJ_Read
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix

/-- `RawJ_DigestRead.initParts` with the PIN2 emission's `r1_wire.DOMAIN` (the same 38 bytes,
`PIN2W7_TranscriptCopy.domain_eq`); `targetPIN2` is the release `target` script verbatim. -/
def initPartsPIN2 (pub : Slice U8) (len : U32) (root : Array U8 32#usize) : Slice (Slice U8) :=
  Array.to_slice (Array.make 5#usize [AspisR1PublicPreparationPIN2.r1_wire.DOMAIN,
    Array.to_slice (Array.make 1#usize [0#u8]),Array.to_slice (core.num.U32.to_le_bytes len),pub,
    Array.to_slice root])

open MultiproofConeCanonical in
theorem targetPIN2 (pub : Slice U8) (len : U32) (root : Array U8 32#usize) :
    BinRawByteCollisionTargets.pred 2 (flatten (initPartsPIN2 pub len root)) =
      some (decodeState root) := by
  rw [BinRawByteCollisionTargets.pred_tail]
  have shape : flatten (initPartsPIN2 pub len root) =
      (MultiproofConeCanonical.bytesOf AspisR1PublicPreparationPIN2.r1_wire.DOMAIN.val ++
        [decodeByte 0#u8] ++ MultiproofConeCanonical.bytesOf (core.num.U32.to_le_bytes len).val ++
        MultiproofConeCanonical.bytesOf pub.val) ++
        bytes (decodeState root) := by
    simp only [initPartsPIN2,flatten,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,
      MultiproofConeCanonical.bytesOf,List.map_append,List.map_cons,List.map_nil,List.append_nil,
      MultiproofConePhysicalTransport.digest_bytes,List.append_assoc]
  rw [shape]
  exact BinRawByteCollisionTargets.trailing_frame _ _

/-- Twin of `RawJ_InitRead.frame` for the PIN2 lift `newTranscript`. -/
theorem init_frame {H : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H) (hash : H)
    (pub : Slice U8) (root : Array U8 32#usize)
    (out : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H)
    (success : erase (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root) = ok (.Ok out)) :
    ∃ frame, Read (observe (run (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root)).1) frame ∧
      BinRawByteCollisionTargets.pred 2 frame = some (decodeState root) := by
  let log := observe (run (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root)).1
  have inc : ∀ frame, Read (observe (run (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root)).1) frame →
      Read log frame := fun _ h => h
  change ∃ frame, Read log frame ∧ _
  unfold AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript at success inc
  obtain ⟨r,hr,s1,sub1⟩ := right_read _ _ _ success
  obtain ⟨r1,hr1,s2,sub2⟩ := right_read _ _ _ s1
  obtain ⟨cf,hcf,s3,sub3⟩ := right_read _ _ _ s2
  cases cf with
  | Break residual =>
    rw [erase_lift] at s3
    repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3 | (solve | (rename_i never; cases never))
  | Continue len =>
    let parts := initPartsPIN2 pub len root
    change erase (effects.digest (AspisR1PublicPreparation.PIN2W7_PrefixGlue.digestBack D) hash parts >>= fun state =>
      pure (core.result.Result.Ok ({state,hash,next_row:=0#u8} : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H))) =
      ok (.Ok out) at s3
    obtain ⟨state,digest,tail⟩ := AuS1_Trace.success_bind _ _ _ s3
    refine ⟨flatten parts,?_,targetPIN2 pub len root⟩
    have member := left_read _ _ _ s3 _
      (RawJ_DigestRead.digest (AspisR1PublicPreparation.PIN2W7_PrefixGlue.digestBack D) hash parts state digest)
    exact inc _ (sub1 _ (sub2 _ (sub3 _ member)))

/-- Twin of `RawJ_PublicRead.frame` for the PIN2 lift `publicTranscript`. -/
theorem public_frame {H : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H) (hash : H)
    (pub : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public) (root : Array U8 32#usize)
    (out : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H)
    (success : erase (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root) = ok (.Ok out)) :
    ∃ frame, Read (observe (run (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root)).1) frame ∧
      BinRawByteCollisionTargets.pred 2 frame = some (decodeState root) := by
  let log := observe (run (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root)).1
  have inc : ∀ frame, Read (observe (run (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root)).1) frame →
      Read log frame := fun _ h => h
  change ∃ frame, Read log frame ∧ _
  unfold AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript at success inc
  obtain ⟨r,hr,s1,sub1⟩ := right_read _ _ _ success
  obtain ⟨r1,hr1,s2,sub2⟩ := right_read _ _ _ s1
  obtain ⟨cf,hcf,s3,sub3⟩ := right_read _ _ _ s2
  cases cf with
  | Break residual =>
    rw [erase_lift] at s3
    repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3 | (solve | (rename_i never; cases never))
  | Continue value =>
    obtain ⟨frame,read,target⟩ := init_frame D hash value.deref root out s3
    exact ⟨frame,inc _ (sub1 _ (sub2 _ (sub3 _ read))),target⟩

/-- `public_frame` read through the copy-back of `publicTranscriptPIN2` (frozen carriers). -/
theorem publicPIN2_frame {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H) (hash : H)
    (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public) (root : Array U8 32#usize)
    (out : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (success : erase (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root) = ok (.Ok out)) :
    ∃ frame, Read (observe (run (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root)).1) frame ∧
      BinRawByteCollisionTargets.pred 2 frame = some (decodeState root) := by
  let log := observe (run (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root)).1
  have inc : ∀ frame, Read (observe (run (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root)).1) frame →
      Read log frame := fun _ h => h
  change ∃ frame, Read log frame ∧ _
  unfold AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 at success inc
  obtain ⟨x,hx,s1,sub1⟩ := right_read _ _ _ success
  cases x with
  | Err e =>
    rw [erase_pure] at s1
    cases s1
  | Ok t =>
    obtain ⟨frame,read,target⟩ := public_frame _ hash _ root t hx
    exact ⟨frame,inc _ (left_read _ _ _ success frame read),target⟩

/-- Twin of `RawJ_VerifyRead.frame` for `verifyPIN2`. -/
theorem verify_frame (F : AspisR1PublicPreparation.S1SemanticCode.Finish) {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public) (input : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (out : AspisR1PublicPreparation.r1_semantic.Verified H)
    (success : erase (AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 F D pub input hash obs) = ok (.Ok out)) :
    ∃ p, AspisR1PublicPreparation.PrefixAdapter.parseAccepted input = ok (.Ok p) ∧
      ∃ frame, Read (observe (run (AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 F D pub input hash obs)).1) frame ∧
        BinRawByteCollisionTargets.pred 2 frame = some (decodeState p.c1_root) := by
  let log := observe (run (AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 F D pub input hash obs)).1
  have inc : ∀ frame, Read (observe (run (AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 F D pub input hash obs)).1) frame →
      Read log frame := fun _ h => h
  change ∃ p, _ ∧ ∃ frame, Read log frame ∧ _
  unfold AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 at success inc
  obtain ⟨r,hr,s1,sub1⟩ := right_read _ _ _ success
  obtain ⟨cf,hcf,s2,sub2⟩ := right_read _ _ _ s1
  cases cf with
  | Break residual =>
    rw [erase_lift] at s2
    repeat' first | (solve | cases s2) | uncase_result | head_reduce s2 | split at s2
  | Continue p =>
    rw [erase_lift] at hr hcf
    cases r with
    | Err error => cases hcf
    | Ok parsed =>
      have same : parsed = p := by simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf
      subst parsed
      obtain ⟨mark,hm,s3,sub3⟩ := right_read _ _ _ s2
      obtain ⟨r1,hr1,s4,sub4⟩ := right_read _ _ _ s3
      obtain ⟨cf1,hcf1,s5,sub5⟩ := right_read _ _ _ s4
      cases cf1 with
      | Break residual =>
        rw [erase_lift] at s5
        repeat' first | (solve | cases s5) | uncase_result | head_reduce s5 | split at s5
      | Continue transcript =>
        rw [erase_lift] at hcf1
        cases r1 with
        | Err error => cases hcf1
        | Ok actual =>
          have same : actual = transcript := by simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf1
          subst actual
          obtain ⟨frame,read,target⟩ := publicPIN2_frame D hash pub p.c1_root transcript hr1
          have member := left_read _ _ _ s3 frame read
          exact ⟨p,hr,frame,inc _ (sub1 _ (sub2 _ (sub3 _ member))),target⟩

#print axioms targetPIN2
#print axioms init_frame
#print axioms public_frame
#print axioms publicPIN2_frame
#print axioms verify_frame
end AspisR1.PIN2_RawJ_Read
end
