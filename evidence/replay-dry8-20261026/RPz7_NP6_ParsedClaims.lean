import RPz7_NP6_RecordShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_ParsedClaims
open Aeneas Aeneas.Std Result AspisR1ClaimsUnrolledParent NP6_StdModel

theorem source_record (pre : ClaimsUnrolledFinish.MainPrefix) (vr : Record)
    (called : ClaimsUnrolledFinish.sourceRecord (ClaimsUnrolledFinish.fromMainPrefix pre) 25#u8 = ok (.Ok vr)) :
    AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 25#u8 =
      ok (.Ok (ClaimsUnrolledFinish.toMainRecord vr)) := by
  have roundtrip : ClaimsUnrolledFinish.toMainPrefix (ClaimsUnrolledFinish.fromMainPrefix pre)=pre := by
    cases pre
    rfl
  unfold ClaimsUnrolledFinish.sourceRecord at called
  rw [roundtrip] at called
  cases h : AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 25#u8 with
  | fail e => simp [h] at called
  | div => simp [h] at called
  | ok result =>
    cases result with
    | Err e => simp [h] at called
    | Ok record =>
      simp only [h,Result.ok.injEq,core.result.Result.Ok.injEq] at called
      cases called
      cases record
      rfl

def Content (reservation : Reservation) (bytes : Slice U8)
    (pre : ClaimsUnrolledFinish.MainPrefix) (out : ClaimsUnrolledFinish.MainClaims) : Prop :=
  reservation = .Ok () ∧ ∃ vr row0 row1 row2,
    (ClaimsUnrolledFinish.external (calls reservation)).validated
      (ClaimsUnrolledFinish.fromMainPrefix pre) 25#u8 = ok (.Ok vr) ∧
    vr.framed.val.length = 3717 ∧
    (ClaimsUnrolledFinish.external (calls reservation)).decode 29#usize vr 0#usize = ok (.Ok row0) ∧
    (ClaimsUnrolledFinish.external (calls reservation)).decode 29#usize vr 29#usize = ok (.Ok row1) ∧
    (ClaimsUnrolledFinish.external (calls reservation)).decode 29#usize vr 58#usize = ok (.Ok row2) ∧
    out.val = [ClaimsUnrolledFinish.toMainArray row0,
      ClaimsUnrolledFinish.toMainArray row1,ClaimsUnrolledFinish.toMainArray row2] ∧
    AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes = ok (.Ok pre)

theorem on_success (reservation : Reservation) (bytes : Slice U8)
    (pre : ClaimsUnrolledFinish.MainPrefix) (out : ClaimsUnrolledFinish.MainClaims)
    (parsed : AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes = ok (.Ok pre))
    (accepted : ClaimsUnrolledFinish.reference (calls reservation) pre = ok (.Ok out)) :
    Content reservation bytes pre out := by
  obtain ⟨allocated,vr,row0,row1,row2,hv,h0,h1,h2,contents⟩ :=
    NP6_ClaimsMain.main_success reservation pre out accepted
  have main := source_record pre vr hv
  have size := NP6_RecordShape.on_parsed_prefix bytes pre (ClaimsUnrolledFinish.toMainRecord vr) parsed main
  exact ⟨allocated,vr,row0,row1,row2,hv,size,h0,h1,h2,contents,parsed⟩

#print axioms source_record
#print axioms on_success
end AspisR1.NP6_ParsedClaims
end
