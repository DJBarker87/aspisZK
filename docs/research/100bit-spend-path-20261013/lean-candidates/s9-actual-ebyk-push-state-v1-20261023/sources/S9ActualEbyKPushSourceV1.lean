import S9ActualEbyKCountSourceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualEbyKPushSourceV1
open AspisR1S9ActualEbyKBackendTransportV1 AspisR1S9ActualEbyKCountSourceV1
open AspisR1S9ActualDotBackendMapV1

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩

/-- Same successful actual two-lane push derives the existing concrete S5
accumulator transition, preserving both raw sum arrays and count. There is no
independent target success, scalar canonicality, value canonicality or history
premise. Source errors remain excluded only by the SAME accepted source run. -/
theorem actual_push_success_source_backend
    (self out : fast_pairing.EbyKDot) (value : NativeW) (scalar : NativeQ)
    (h : fast_pairing.EbyKDot.push self value scalar = .ok (.Ok (),out)) :
    AspisR1EbyKPushDotBackend.pushWithDotBackend actualRaw
      (toSourceState self) (toSourceWide value) (toSourceQ scalar) =
      .ok (.Ok (),toSourceState out) := by
  unfold fast_pairing.EbyKDot.push at h
  split at h
  · cases h
  · rename_i hcount
    obtain ⟨arr,hfrom,h⟩ := bind_success _ _ _ h
    obtain ⟨lo,hlo,h⟩ := bind_success _ _ _ h
    obtain ⟨hi,hhi,h⟩ := bind_success _ _ _ h
    obtain ⟨checked,hchecked,h⟩ := bind_success _ _ _ h
    cases checked with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
      cases h
    | Ok q =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨d0,hd0,h⟩ := bind_success _ _ _ h
      obtain ⟨d1,hd1,h⟩ := bind_success _ _ _ h
      simp only [lift,bind_tc_ok] at h
      have hout : ({c0:=d0,c1:=d1,count:=Usize.wrapping_add self.count 1#usize} : fast_pairing.EbyKDot)=out :=
        congrArg Prod.snd (Result.ok.inj h)
      have hsFrom := (native_from_wide_source value).symm.trans hfrom
      have hsChecked := native_checked_q_success_to_source scalar q hchecked
      have hsDot0 := native_dot_push_success_backend self.c0 d0 lo q hd0
      have hsDot1 := native_dot_push_success_backend self.c1 d1 hi q hd1
      have hc : self.count < fast_pairing.MAX_TERMS := lt_of_not_ge hcount
      have hadd := checked_count_add_eq_wrapping self.count hc
      have hcountOld : ¬ self.count ≥ AspisR1EbyKPushExplicitOpsV1.maxTerms := by
        simpa only [toSourceState,fast_pairing.MAX_TERMS,AspisR1EbyKPushExplicitOpsV1.maxTerms] using hcount
      rw [←hout]
      unfold AspisR1EbyKPushDotBackend.pushWithDotBackend
        AspisR1EbyKPushConcreteCheckedQV1.pushWithConcreteCheckedQ
        AspisR1EbyKPushSourceConversionV1.pushWithSourceCheckedAdd
        AspisR1EbyKPushSourceConversionV1.pushWithSourceConversion
        AspisR1EbyKPushExplicitOpsV1.pushWithOps
      simp only [hsFrom,bind_tc_ok,hlo,hhi,hsChecked,
        core.result.Result.Insts.CoreOpsTry.branch,hsDot0,hsDot1,hadd,
        toSourceState,toSourceDot,bind_tc_ok]
      rw [if_neg hcountOld]

#print axioms actual_push_success_source_backend
end AspisR1S9ActualEbyKPushSourceV1
