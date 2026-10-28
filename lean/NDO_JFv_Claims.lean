import NDO_JFv_ClaimsRows
set_option autoImplicit false
namespace AspisR1.JFv_Claims
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem success (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) :
    ∃ out,ClaimsUnrolledFinish.reference (NP6_StdModel.calls (.Ok ())) pre=ok (.Ok out) := by
  obtain ⟨vr,r0,r1,r2,call,h0,h1,h2⟩ := JFv_ClaimsRows.success bytes pre parsed
  let record : AspisR1ClaimsUnrolledParent.Record := ⟨vr.row,vr.framed⟩
  have recordEq : ClaimsUnrolledFinish.toMainRecord record=vr := by cases vr;rfl
  have prefixEq : ClaimsUnrolledFinish.toMainPrefix (ClaimsUnrolledFinish.fromMainPrefix pre)=pre := by cases pre;rfl
  have getter : ClaimsUnrolledFinish.sourceRecord (ClaimsUnrolledFinish.fromMainPrefix pre) 25#u8=ok (.Ok record) := by
    unfold ClaimsUnrolledFinish.sourceRecord
    rw [prefixEq,call]
  have d0 : ClaimsUnrolledFinish.sourceDecode 29#usize record 0#usize=ok (.Ok (ClaimsUnrolledFinish.fromMainArray r0)) := by
    unfold ClaimsUnrolledFinish.sourceDecode
    rw [recordEq,h0]
  have d1 : ClaimsUnrolledFinish.sourceDecode 29#usize record 29#usize=ok (.Ok (ClaimsUnrolledFinish.fromMainArray r1)) := by
    unfold ClaimsUnrolledFinish.sourceDecode
    rw [recordEq,h1]
  have d2 : ClaimsUnrolledFinish.sourceDecode 29#usize record 58#usize=ok (.Ok (ClaimsUnrolledFinish.fromMainArray r2)) := by
    unfold ClaimsUnrolledFinish.sourceDecode
    rw [recordEq,h2]
  unfold ClaimsUnrolledFinish.reference
  rw [NP6_ClaimsModel.reference_normalized]
  simp only [NP6_ClaimsModel.normalized,ClaimsUnrolledFinish.external,getter,bind_tc_ok,
    AspisR1ClaimsUnrolledParent.decodeRows,d0,d1,d2,core.result.Result.Insts.CoreOpsTry.branch]
  exact ⟨_,rfl⟩

#print axioms success
end AspisR1.JFv_Claims
