import ExtractedVerifyFinishModel
import ExtractedDigest32Callers
import ExtractedSourceFull25Frames
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.CircleCalls
open r1_wire TranscriptStep
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Actual row25 circle success reaches its three-call transcript step. -/
theorem circle25_success {H : Type} (B : FinishModel.Boundaries) (D : aspis_core.Digest32 H)
    (self after : SemanticTranscript H) (record : ValidatedRecord)
    (point : aspis_core.circle.SecureCirclePoint) (hrow : record.row = 25#u8)
    (h : FinishModel.circle_validated B D self record = ok (.Ok point,after)) :
    ∃ block, SemanticTranscript.sample_block_validated D self 25#u8 record.framed =
      ok (.Ok block,after) ∧ B.circle block FinishModel.CircleRow.First = ok point := by
  simp only [FinishModel.circle_validated,ValidatedRecord.impl.row,
    ValidatedRecord.impl.framed,hrow,bind_tc_ok] at h
  obtain ⟨⟨ret,mid⟩,hs,h⟩ := bind_success _ _ _ h
  cases ret with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,bind_tc_ok] at h
    cases h
  | Ok block =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    change (do let value ← B.circle block FinishModel.CircleRow.First
               ok ((core.result.Result.Ok value : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error),mid)) =
      ok (.Ok point,after) at h
    obtain ⟨value,hvalue,h⟩ := bind_success _ _ _ h
    have hp := Result.ok.inj h
    have hq : value = point := core.result.Result.Ok.inj (congrArg Prod.fst hp)
    have ht : mid = after := congrArg Prod.snd hp
    exact ⟨block,by simpa only [ht] using hs,by simpa only [hq] using hvalue⟩

theorem circle25_step {H : Type} (B : FinishModel.Boundaries) (D : aspis_core.Digest32 H)
    (self after : SemanticTranscript H) (record : ValidatedRecord)
    (point : aspis_core.circle.SecureCirclePoint) (hrow : record.row = 25#u8)
    (h : FinishModel.circle_validated B D self record = ok (.Ok point,after)) :
    self.next_row = 25#u8 ∧ ∃ block tag next absorbed state,
      tag.val = 160 + 25 ∧ next.val = 26 ∧
      D.digest self.hash (absorbParts self.state tag record.framed) = ok absorbed ∧
      D.digest self.hash (readParts absorbed 1#u8) = ok block ∧
      D.digest self.hash (readParts absorbed 2#u8) = ok state ∧
      B.circle block FinishModel.CircleRow.First = ok point ∧
      after = {self with state,next_row := next} := by
  obtain ⟨block,hs,hpoint⟩ := circle25_success B D self after record point hrow h
  obtain ⟨hr,tag,next,absorbed,state,ht,hn,ha,hb,hc,he⟩ :=
    TranscriptStep.step_success D self after 25#u8 record.framed block (by decide) hs
  exact ⟨hr.symm,block,tag,next,absorbed,state,ht,hn,ha,hb,hc,hpoint,he⟩
theorem circle25_record_bytes (pre : Prefix) (record : ValidatedRecord)
    (h : Prefix.validated_record pre 25#u8 = ok (.Ok record)) :
    record.row = 25#u8 ∧ pre.records.val[25]? = some record.framed :=
  SourceFull25.validated_record_bytes pre 25#u8 record h
#print axioms circle25_record_bytes
#print axioms circle25_success
#print axioms circle25_step
/-- Actual row26 circle success reaches its three-call transcript step. -/
theorem circle26_success {H : Type} (B : FinishModel.Boundaries) (D : aspis_core.Digest32 H)
    (self after : SemanticTranscript H) (record : ValidatedRecord)
    (point : aspis_core.circle.SecureCirclePoint) (hrow : record.row = 26#u8)
    (h : FinishModel.circle_validated B D self record = ok (.Ok point,after)) :
    ∃ block, SemanticTranscript.sample_block_validated D self 26#u8 record.framed =
      ok (.Ok block,after) ∧ B.circle block FinishModel.CircleRow.Second = ok point := by
  simp only [FinishModel.circle_validated,ValidatedRecord.impl.row,
    ValidatedRecord.impl.framed,hrow,bind_tc_ok] at h
  obtain ⟨⟨ret,mid⟩,hs,h⟩ := bind_success _ _ _ h
  cases ret with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,bind_tc_ok] at h
    cases h
  | Ok block =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    change (do let value ← B.circle block FinishModel.CircleRow.Second
               ok ((core.result.Result.Ok value : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error),mid)) =
      ok (.Ok point,after) at h
    obtain ⟨value,hvalue,h⟩ := bind_success _ _ _ h
    have hp := Result.ok.inj h
    have hq : value = point := core.result.Result.Ok.inj (congrArg Prod.fst hp)
    have ht : mid = after := congrArg Prod.snd hp
    exact ⟨block,by simpa only [ht] using hs,by simpa only [hq] using hvalue⟩

theorem circle26_step {H : Type} (B : FinishModel.Boundaries) (D : aspis_core.Digest32 H)
    (self after : SemanticTranscript H) (record : ValidatedRecord)
    (point : aspis_core.circle.SecureCirclePoint) (hrow : record.row = 26#u8)
    (h : FinishModel.circle_validated B D self record = ok (.Ok point,after)) :
    self.next_row = 26#u8 ∧ ∃ block tag next absorbed state,
      tag.val = 160 + 26 ∧ next.val = 27 ∧
      D.digest self.hash (absorbParts self.state tag record.framed) = ok absorbed ∧
      D.digest self.hash (readParts absorbed 1#u8) = ok block ∧
      D.digest self.hash (readParts absorbed 2#u8) = ok state ∧
      B.circle block FinishModel.CircleRow.Second = ok point ∧
      after = {self with state,next_row := next} := by
  obtain ⟨block,hs,hpoint⟩ := circle26_success B D self after record point hrow h
  obtain ⟨hr,tag,next,absorbed,state,ht,hn,ha,hb,hc,he⟩ :=
    TranscriptStep.step_success D self after 26#u8 record.framed block (by decide) hs
  exact ⟨hr.symm,block,tag,next,absorbed,state,ht,hn,ha,hb,hc,hpoint,he⟩
theorem circle26_record_bytes (pre : Prefix) (record : ValidatedRecord)
    (h : Prefix.validated_record pre 26#u8 = ok (.Ok record)) :
    record.row = 26#u8 ∧ pre.records.val[26]? = some record.framed :=
  SourceFull25.validated_record_bytes pre 26#u8 record h
#print axioms circle26_record_bytes
#print axioms circle26_success
#print axioms circle26_step
end AspisR1PublicPreparation.CircleCalls
