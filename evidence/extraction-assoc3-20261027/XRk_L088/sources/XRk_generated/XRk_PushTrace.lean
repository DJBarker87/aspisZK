import XRk_CanonicalScalar
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRk_PushTrace
theorem accepted (old next : fast_pairing.EbyKDot)
    (e : aspis_core.field.wide_exact.WideExact) (q : aspis_core.field.QM31)
    (run : fast_pairing.EbyKDot.push old e q=ok (.Ok (),next)) :
    XRk_CanonicalScalar.Canonical q ∧
    ∃ (wide : Array fast_pairing.canonical.Q 2#usize) (a b raw : fast_pairing.canonical.Q),
      fast_pairing.canonical.Q.from_wide e=ok wide ∧
      Array.index_usize wide 0#usize=ok a ∧ Array.index_usize wide 1#usize=ok b ∧
      fast_pairing.checked_q q=ok (.Ok raw) ∧
      fast_pairing.canonical.Dot.push old.c0 a raw=ok next.c0 ∧
      fast_pairing.canonical.Dot.push old.c1 b raw=ok next.c1 ∧
      old.count+1#usize=ok next.count := by
  unfold fast_pairing.EbyKDot.push at run
  split at run
  · cases run
  · obtain ⟨wide,hwide,run⟩ := bind_success _ _ _ run
    obtain ⟨a,ha,run⟩ := bind_success _ _ _ run
    obtain ⟨b,hb,run⟩ := bind_success _ _ _ run
    obtain ⟨r,hchecked,run⟩ := bind_success _ _ _ run
    cases r with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at run
      cases run
    | Ok raw =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      obtain ⟨d0,hd0,run⟩ := bind_success _ _ _ run
      obtain ⟨d1,hd1,run⟩ := bind_success _ _ _ run
      obtain ⟨count,hcount,run⟩ := bind_success _ _ _ run
      have same := congrArg Prod.snd (Result.ok.inj run)
      change ({c0:=d0,c1:=d1,count:=count} : fast_pairing.EbyKDot)=next at same
      subst next
      exact ⟨XRk_CanonicalScalar.checked q raw hchecked,wide,a,b,raw,hwide,ha,hb,hchecked,hd0,hd1,hcount⟩
#print axioms accepted
end XRk_PushTrace
