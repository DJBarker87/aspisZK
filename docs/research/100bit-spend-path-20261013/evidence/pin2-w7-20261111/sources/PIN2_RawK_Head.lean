import RPz8_RawK_VerifyHead
import PIN2_RawJ_Read
/-! PIN2 W9 (2026-11-11): twins of the release RawK_InitHead.first/address_tag,
RawK_PublicHead.first and RawK_VerifyHead.first at the PIN2 levels: the PIN2 lift
`newTranscript` (`init_first`, over `PIN2_RawJ_Read.initPartsPIN2`), the PIN2 lift
`publicTranscript` (`public_first`), `publicTranscriptPIN2` (`publicPIN2_first`: one extra
step for the pure copy-back) and `verifyPIN2` (`verify_first`).  Each proof is the release
tactic script with the PIN2 names; conclusions as in the release (first log entry exists and
starts with byte 85). -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PIN2_RawK_Head
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix

/-- Twin of `RawK_InitHead.first` for the PIN2 lift `newTranscript`. -/
theorem init_first {H : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H) (hash : H)
    (pub : Slice U8) (root : Array U8 32#usize) (out : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H)
    (success : erase (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root) = ok (.Ok out)) :
    ∃ len state,
      RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root) =
        some (flatten (PIN2_RawJ_Read.initPartsPIN2 pub len root),state) := by
  let log := RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root)
  have inc : ∀ entry, RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root) = some entry →
      log = some entry := fun _ h => h
  change ∃ len state, log = _
  unfold AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript at success inc
  obtain ⟨r,hr,s1,sub1⟩ := RawK_Head.right _ _ _ success
  obtain ⟨r1,hr1,s2,sub2⟩ := RawK_Head.right _ _ _ s1
  obtain ⟨cf,hcf,s3,sub3⟩ := RawK_Head.right _ _ _ s2
  cases cf with
  | Break residual =>
    rw [erase_lift] at s3
    repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3 | (solve | (rename_i never; cases never))
  | Continue len =>
    let parts := PIN2_RawJ_Read.initPartsPIN2 pub len root
    change erase (effects.digest (AspisR1PublicPreparation.PIN2W7_PrefixGlue.digestBack D) hash parts >>= fun state =>
      pure (core.result.Result.Ok ({state,hash,next_row:=0#u8} : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H))) =
      ok (.Ok out) at s3
    obtain ⟨state,digest,tail,logs⟩ := AuS1_Trace.success_bind _ _ _ s3
    exact ⟨len,decodeState state,inc _ (sub1 _ (sub2 _ (sub3 _
      (RawK_Head.left _ _ _ s3 _ (RawK_Head.digest_head (AspisR1PublicPreparation.PIN2W7_PrefixGlue.digestBack D)
        hash parts state digest)))))⟩

/-- Twin of `RawK_InitHead.address_tag` over the PIN2 domain bytes. -/
theorem address_tag (pub : Slice U8) (len : U32) (root : Array U8 32#usize) :
    (flatten (PIN2_RawJ_Read.initPartsPIN2 pub len root)).head? = some 85 := by
  simp only [PIN2_RawJ_Read.initPartsPIN2,flatten,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil]
  unfold AspisR1PublicPreparationPIN2.r1_wire.DOMAIN
  rfl

/-- Twin of `RawK_PublicHead.first` for the PIN2 lift `publicTranscript`. -/
theorem public_first {H : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H) (hash : H)
    (pub : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public) (root : Array U8 32#usize)
    (out : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H)
    (success : erase (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root) = ok (.Ok out)) :
    ∃ entry, RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root) = some entry ∧
      entry.1.head? = some 85 := by
  let log := RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root)
  have inc : ∀ entry, RawK_Head.head (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root) = some entry →
      log = some entry := fun _ h => h
  change ∃ entry, log = some entry ∧ _
  unfold AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript at success inc
  obtain ⟨r,hr,s1,sub1⟩ := RawK_Head.right _ _ _ success
  obtain ⟨r1,hr1,s2,sub2⟩ := RawK_Head.right _ _ _ s1
  obtain ⟨cf,hcf,s3,sub3⟩ := RawK_Head.right _ _ _ s2
  cases cf with
  | Break residual =>
    rw [erase_lift] at s3
    repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3 | (solve | (rename_i never; cases never))
  | Continue value =>
    obtain ⟨len,state,h⟩ := init_first D hash value.deref root out s3
    exact ⟨_,inc _ (sub1 _ (sub2 _ (sub3 _ h))),address_tag _ _ _⟩

/-- `public_first` read through the copy-back of `publicTranscriptPIN2` (frozen carriers). -/
theorem publicPIN2_first {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H) (hash : H)
    (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public) (root : Array U8 32#usize)
    (out : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (success : erase (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root) = ok (.Ok out)) :
    ∃ entry, RawK_Head.head (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root) = some entry ∧
      entry.1.head? = some 85 := by
  let log := RawK_Head.head (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root)
  have inc : ∀ entry, RawK_Head.head (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root) = some entry →
      log = some entry := fun _ h => h
  change ∃ entry, log = some entry ∧ _
  unfold AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 at success inc
  obtain ⟨x,hx,s1,sub1⟩ := AuS1_Trace.success_bind _ _ _ success
  cases x with
  | Err e =>
    rw [erase_pure] at s1
    cases s1
  | Ok t =>
    obtain ⟨entry,read,tag⟩ := public_first _ hash _ root t hx
    exact ⟨entry,inc _ (RawK_Head.left _ _ _ success entry read),tag⟩

/-- Twin of `RawK_VerifyHead.first` for `verifyPIN2`. -/
theorem verify_first (F : AspisR1PublicPreparation.S1SemanticCode.Finish) {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public) (input : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (out : AspisR1PublicPreparation.r1_semantic.Verified H)
    (success : erase (AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 F D pub input hash obs) = ok (.Ok out)) :
    ∃ entry, RawK_Head.head (AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 F D pub input hash obs) = some entry ∧
      entry.1.head? = some 85 := by
  let log := RawK_Head.head (AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 F D pub input hash obs)
  have inc : ∀ entry, RawK_Head.head (AspisR1PublicPreparation.S1SemanticCode.verifyPIN2 F D pub input hash obs) = some entry →
      log = some entry := fun _ h => h
  change ∃ entry, log = some entry ∧ _
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
          obtain ⟨entry,read,tag⟩ := publicPIN2_first D hash pub p.c1_root transcript hr1
          have member := RawK_Head.left _ _ _ s3 entry read
          exact ⟨entry,inc _ (sub1 _ (sub2 _ (sub3 _ member))),tag⟩

#print axioms init_first
#print axioms address_tag
#print axioms public_first
#print axioms publicPIN2_first
#print axioms verify_first
end AspisR1.PIN2_RawK_Head
end
