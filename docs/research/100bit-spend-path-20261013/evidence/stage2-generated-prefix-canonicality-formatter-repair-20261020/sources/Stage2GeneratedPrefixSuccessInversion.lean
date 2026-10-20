import AspisR1Stage2AdoptedResume.Funs
import Stage2GeneratedPrefixReaderBridgeProof

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2AdoptedReader.GeneratedPrefixSuccessInversion

abbrev GWide := AspisR1Stage2AdoptedResume.aspis_core.field.WideExact
abbrev GQM := AspisR1Stage2AdoptedResume.aspis_core.field.QM31
abbrev GReader := AspisR1Stage2AdoptedResume.verifier.Reader

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem generated_wide_success (r r' : GReader) (value : GWide)
    (h : AspisR1Stage2AdoptedResume.verifier.Reader.e r = ok (.Ok value, r')) :
    ∃ bytes : Array Std.U8 32#usize,
      AspisR1Stage2AdoptedResume.verifier.Reader.raw 32#usize r = ok (bytes, r') ∧
      AspisR1Stage2AdoptedResume.aspis_core.field.WideExact.from_le_bytes bytes.to_slice =
        ok (some value) := by
  unfold AspisR1Stage2AdoptedResume.verifier.Reader.e at h
  obtain ⟨pair, hp, h⟩ := bind_success _ _ _ h
  rcases pair with ⟨bytes, rr⟩
  simp only [lift, bind_tc_ok] at h
  obtain ⟨o, ho, h⟩ := bind_success _ _ _ h
  have h32 : decide (32 ≤ UScalar.cMax UScalarTy.Usize) = true := by decide
  cases o with
  | none =>
      simp only [AspisR1Stage2AdoptedResume.core.option.Option.ok_or, bind_tc_ok, h32] at h
      cases h
  | some v =>
      simp only [AspisR1Stage2AdoptedResume.core.option.Option.ok_or, bind_tc_ok, h32, Result.ok.injEq,
        Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨hv, hr⟩ := h
      subst v
      subst rr
      exact ⟨bytes, hp, ho⟩

theorem generated_qm_success (r r' : GReader) (value : GQM)
    (h : AspisR1Stage2AdoptedResume.verifier.Reader.k r = ok (.Ok value, r')) :
    ∃ bytes : Array Std.U8 16#usize,
      AspisR1Stage2AdoptedResume.verifier.Reader.raw 16#usize r = ok (bytes, r') ∧
      AspisR1Stage2AdoptedResume.aspis_core.field.QM31.from_le_bytes bytes.to_slice =
        ok (some value) := by
  unfold AspisR1Stage2AdoptedResume.verifier.Reader.k at h
  obtain ⟨pair, hp, h⟩ := bind_success _ _ _ h
  rcases pair with ⟨bytes, rr⟩
  simp only [lift, bind_tc_ok] at h
  obtain ⟨o, ho, h⟩ := bind_success _ _ _ h
  have h16 : decide (16 ≤ UScalar.cMax UScalarTy.Usize) = true := by decide
  cases o with
  | none =>
      simp only [AspisR1Stage2AdoptedResume.core.option.Option.ok_or, bind_tc_ok, h16] at h
      cases h
  | some v =>
      simp only [AspisR1Stage2AdoptedResume.core.option.Option.ok_or, bind_tc_ok, h16, Result.ok.injEq,
        Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨hv, hr⟩ := h
      subst v
      subst rr
      exact ⟨bytes, hp, ho⟩

#print axioms generated_wide_success
#print axioms generated_qm_success

end AspisR1Stage2AdoptedReader.GeneratedPrefixSuccessInversion
