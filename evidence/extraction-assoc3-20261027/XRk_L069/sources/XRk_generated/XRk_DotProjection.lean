import XRk_Association
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRk_DotProjection
theorem push_count (old next : fast_pairing.EbyKDot)
    (e : aspis_core.field.wide_exact.WideExact) (q : aspis_core.field.QM31)
    (run : fast_pairing.EbyKDot.push old e q = ok (.Ok (),next)) :
    old.count < 4096#usize ∧ old.count + 1#usize = ok next.count := by
  unfold fast_pairing.EbyKDot.push at run
  split at run
  · cases run
  · rename_i below
    obtain ⟨limbs,_,run⟩ := bind_success _ _ _ run
    obtain ⟨a,_,run⟩ := bind_success _ _ _ run
    obtain ⟨b,_,run⟩ := bind_success _ _ _ run
    obtain ⟨r,_,run⟩ := bind_success _ _ _ run
    cases r with
    | Err err =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at run
      cases run
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      obtain ⟨a,_,run⟩ := bind_success _ _ _ run
      obtain ⟨b,_,run⟩ := bind_success _ _ _ run
      obtain ⟨count,hcount,run⟩ := bind_success _ _ _ run
      have same := congrArg Prod.snd (Result.ok.inj run)
      have counts := congrArg fast_pairing.EbyKDot.count same
      change count=next.count at counts
      refine ⟨?_,hcount.trans (congrArg Result.ok counts)⟩
      simpa only [fast_pairing.MAX_TERMS] using (lt_of_not_ge below)
#print axioms push_count
end XRk_DotProjection
