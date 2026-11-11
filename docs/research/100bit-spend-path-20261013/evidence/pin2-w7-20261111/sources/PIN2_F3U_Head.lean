import RPz8_F3U_VerifyHead
import PIN2_RawK_Head
/-! PIN2 W9 (2026-11-11): twins of the release F3U_InitCall.reached, F3U_InitAddress.head,
F3U_PublicHead.first and F3U_VerifyHead.first at the PIN2 levels (PIN2 lift `newTranscript`,
PIN2 lift `publicTranscript`, `publicTranscriptPIN2`, `verifyPIN2`).  Each proof is the
release tactic script with the PIN2 names (PCWN_NewLib `map_err` in the conversion step).
Only change of meaning: the `public_bytes` conjunct is the PIN2 emission's serializer
(of `PreparationBinding.toPIN2 pub` at the frozen-carrier levels), since that is the
serializer the PIN2 verifier runs; the head frame is unchanged
(`PublicInitFrame.frame (rawBytes encoded.deref) ...`). -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PIN2_F3U_Head
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1PublicPreparation.SourceDigestAddresses

/-- Twin of `F3U_InitCall.reached` for the PIN2 lift `newTranscript`. -/
theorem init_reached {H : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H) (hash : H)
    (pub : Slice U8) (root : Array U8 32#usize) (out : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H)
    (success : erase (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root) = ok (.Ok out)) :
    ∃ (len : U32) (state : State),
      core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len pub)=ok (.Ok len) ∧
      RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root)=
        some (flatten (PIN2_RawJ_Read.initPartsPIN2 pub len root),state) := by
  let log := RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root)
  have inc : ∀ entry, RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root)=some entry →
      log=some entry := fun _ h=>h
  change ∃ len state, _ ∧ log=_
  unfold AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript at success inc
  obtain ⟨r,hr,s1,sub1⟩ := RawK_Head.right _ _ _ success
  obtain ⟨r1,hr1,s2,sub2⟩ := RawK_Head.right _ _ _ s1
  obtain ⟨cf,hcf,s3,sub3⟩ := RawK_Head.right _ _ _ s2
  cases cf with
  | Break residual =>
    rw [erase_lift] at s3
    repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3 | (solve | (rename_i never; cases never))
  | Continue len =>
    have converted : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len pub)=ok (.Ok len) := by
      rw [erase_lift] at hr hr1 hcf
      cases r1 with
      | Err e => cases hcf
      | Ok n =>
        have same : n=len := core.ops.control_flow.ControlFlow.Continue.inj (Result.ok.inj hcf)
        subst n
        cases r with
        | Err e =>
          cases he : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once D () e <;>
            simp [PCWN_NewLib.core.result.Result.map_err,he] at hr1
        | Ok n =>
          simp only [PCWN_NewLib.core.result.Result.map_err] at hr1
          have same : n=len := core.result.Result.Ok.inj (Result.ok.inj hr1)
          rw [same] at hr
          exact hr
    let parts := PIN2_RawJ_Read.initPartsPIN2 pub len root
    change erase (effects.digest (AspisR1PublicPreparation.PIN2W7_PrefixGlue.digestBack D) hash parts >>= fun state =>
      pure (core.result.Result.Ok ({state,hash,next_row:=0#u8} : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H)))=
      ok (.Ok out) at s3
    obtain ⟨state,digest,tail,logs⟩ := AuS1_Trace.success_bind _ _ _ s3
    exact ⟨len,decodeState state,converted,inc _ (sub1 _ (sub2 _ (sub3 _
      (RawK_Head.left _ _ _ s3 _ (RawK_Head.digest_head (AspisR1PublicPreparation.PIN2W7_PrefixGlue.digestBack D)
        hash parts state digest)))))⟩

/-- The PIN2 domain bytes are the release ones, so the two init part lists flatten alike. -/
theorem flatten_initPartsPIN2 (pub : Slice U8) (len : U32) (root : Array U8 32#usize) :
    flatten (PIN2_RawJ_Read.initPartsPIN2 pub len root) = flatten (RawJ_DigestRead.initParts pub len root) := by
  unfold PIN2_RawJ_Read.initPartsPIN2 RawJ_DigestRead.initParts
  rw [AspisR1PublicPreparation.PIN2W7_TranscriptCopy.domain_eq]

/-- Twin of `F3U_InitAddress.head` for the PIN2 lift `newTranscript`. -/
theorem init_head {H : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H) (hash : H)
    (pub : Slice U8) (root : Array U8 32#usize) (out : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H)
    (success : erase (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root)=ok (.Ok out)) :
    ∃ state, RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root)=
      some (AspisR1.PublicInitFrame.frame (rawBytes pub) (decodeState root),state) := by
  obtain ⟨len,state,converted,first⟩ := init_reached D hash pub root out success
  have address := AspisR1PublicPreparation.SourceDigestAddresses.flatten_init pub root len
  change flatten (RawJ_DigestRead.initParts pub len root)=_ at address
  rw [AspisR1PublicPreparation.SourceDigestAddresses.successful_length pub len converted] at address
  change flatten (RawJ_DigestRead.initParts pub len root)=
    AspisR1.PublicInitFrame.frame (rawBytes pub) (decodeState root) at address
  rw [← flatten_initPartsPIN2] at address
  exact ⟨state,address ▸ first⟩

/-- Twin of `F3U_PublicHead.first` for the PIN2 lift `publicTranscript`. -/
theorem public_first {H : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H) (hash : H)
    (pub : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public) (root : Array U8 32#usize)
    (out : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H)
    (success : erase (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root)=ok (.Ok out)) :
    ∃ (encoded : alloc.vec.Vec U8) (state : State),
      AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub=ok (.Ok encoded) ∧
      RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root)=
        some (AspisR1.PublicInitFrame.frame (rawBytes encoded.deref) (decodeState root),state) := by
  let log := RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root)
  have inc : ∀ entry, RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root)=some entry →
      log=some entry := fun _ h=>h
  change ∃ encoded state, _ ∧ log=_
  unfold AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript at success inc
  obtain ⟨r,hr,s1,sub1⟩ := RawK_Head.right _ _ _ success
  obtain ⟨r1,hr1,s2,sub2⟩ := RawK_Head.right _ _ _ s1
  obtain ⟨cf,hcf,s3,sub3⟩ := RawK_Head.right _ _ _ s2
  cases cf with
  | Break residual =>
    rw [erase_lift] at s3
    repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3 | (solve | (rename_i never; cases never))
  | Continue encoded =>
    have serialized : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub=ok (.Ok encoded) := by
      rw [erase_lift] at hr hr1 hcf
      cases r1 with
      | Err e => cases hcf
      | Ok n =>
        have same : n=encoded := core.ops.control_flow.ControlFlow.Continue.inj (Result.ok.inj hcf)
        subst n
        cases r with
        | Err e =>
          cases he : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once D () e <;>
            simp [PCWN_NewLib.core.result.Result.map_err,he] at hr1
        | Ok n =>
          simp only [PCWN_NewLib.core.result.Result.map_err] at hr1
          have same : n=encoded := core.result.Result.Ok.inj (Result.ok.inj hr1)
          rw [same] at hr
          exact hr
    obtain ⟨state,head⟩ := init_head D hash encoded.deref root out s3
    exact ⟨encoded,state,serialized,inc _ (sub1 _ (sub2 _ (sub3 _ head)))⟩

/-- `public_first` read through the copy-back of `publicTranscriptPIN2` (frozen carriers). -/
theorem publicPIN2_first {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H) (hash : H)
    (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public) (root : Array U8 32#usize)
    (out : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (success : erase (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root)=ok (.Ok out)) :
    ∃ (encoded : alloc.vec.Vec U8) (state : State),
      AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (AspisR1PublicPreparation.PreparationBinding.toPIN2 pub)=ok (.Ok encoded) ∧
      RawK_Head.head (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root)=
        some (AspisR1.PublicInitFrame.frame (rawBytes encoded.deref) (decodeState root),state) := by
  let log := RawK_Head.head (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root)
  have inc : ∀ entry, RawK_Head.head (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root)=some entry →
      log=some entry := fun _ h=>h
  change ∃ encoded state, _ ∧ log=_
  unfold AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 at success inc
  obtain ⟨x,hx,s1,sub1⟩ := AuS1_Trace.success_bind _ _ _ success
  cases x with
  | Err e =>
    rw [erase_pure] at s1
    cases s1
  | Ok t =>
    obtain ⟨encoded,state,serialized,read⟩ := public_first _ hash _ root t hx
    exact ⟨encoded,state,serialized,inc _ (RawK_Head.left _ _ _ success _ read)⟩

/-- Twin of `F3U_VerifyHead.first` for `verifyPIN2`. -/
theorem verify_first (F : AspisR1PublicPreparation.S1SemanticCode.Finish) {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public) (input : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (out : AspisR1PublicPreparation.r1_semantic.Verified H)
    (success : erase (AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 F D pub input hash obs) = ok (.Ok out)) :
    ∃ (encoded : alloc.vec.Vec U8) (root state : State),
      AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (AspisR1PublicPreparation.PreparationBinding.toPIN2 pub)=ok (.Ok encoded) ∧
      RawK_Head.head (AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 F D pub input hash obs)=
        some (AspisR1.PublicInitFrame.frame (AspisR1PublicPreparation.SourceDigestAddresses.rawBytes encoded.deref) root,state) := by
  let log := RawK_Head.head (AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 F D pub input hash obs)
  have inc : ∀ entry, RawK_Head.head (AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 F D pub input hash obs)=some entry →
      log=some entry := fun _ h=>h
  change ∃ encoded root state, _ ∧ log=_
  unfold AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 at success inc
  obtain ⟨r,hr,s1,sub1⟩  := RawK_Head.right _ _ _ success
  obtain ⟨cf,hcf,s2,sub2⟩  := RawK_Head.right _ _ _ s1
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
      obtain ⟨mark,hm,s3,sub3⟩  := RawK_Head.right _ _ _ s2
      obtain ⟨r1,hr1,s4,sub4⟩ := AuS1_Trace.success_bind _ _ _ s3
      obtain ⟨cf1,hcf1,s5,sub5⟩  := RawK_Head.right _ _ _ s4
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
          obtain ⟨encoded,state,serialized,read⟩ := publicPIN2_first D hash pub p.c1_root transcript hr1
          have member := RawK_Head.left _ _ _ s3 _ read
          exact ⟨encoded,decodeState p.c1_root,state,serialized,inc _ (sub1 _ (sub2 _ (sub3 _ member)))⟩

#print axioms init_reached
#print axioms flatten_initPartsPIN2
#print axioms init_head
#print axioms public_first
#print axioms publicPIN2_first
#print axioms verify_first
end AspisR1.PIN2_F3U_Head
end
