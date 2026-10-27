import XSe_WideVariant
import XRz_HybridPrepare
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSe_PrepareCuts
/-- Variant provenance from the actual expanded-buffer wide_view call and
same hybrid preparation, with no independently supplied successful child. -/
theorem source (low : XRz_HybridSampler.Low) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (g scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) (out : verifier.Prepared)
 (run : XRz_HybridPrepare.prepare low D pub proof hash obs g=ok (.Ok out,scratch)) :
 ∃ (semantic y1 : Slice U8) (v : verifier.View) (sem : r1_semantic.Verified H),
 verifier.candidate.wide_view proof semantic y1=ok (.Ok v) ∧
 XRz_HybridPrepared.prepared low D sem v hash g=ok (.Ok out,scratch) := by
 unfold XRz_HybridPrepare.prepare at run
 obtain ⟨n,_,run⟩ := bind_success _ _ _ run
 obtain ⟨m,_,run⟩ := bind_success _ _ _ run
 obtain ⟨size,_,run⟩ := bind_success _ _ _ run
 obtain ⟨raw,_,run⟩ := bind_success _ _ _ run
 obtain ⟨r,_,run⟩ := bind_success _ _ _ run
 cases r with
 | Err e =>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from,bind_tc_ok] at run
   cases run
 | Ok buffer =>
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
  obtain ⟨s,back,_,run⟩ := pair_bind_success _ _ _ run
  obtain ⟨pair,restore,_,run⟩ := pair_bind_success _ _ _ run
  rcases pair with ⟨semantic,y1⟩
  obtain ⟨off,_,run⟩ := bind_success _ _ _ run
  obtain ⟨input,_,run⟩ := bind_success _ _ _ run
  obtain ⟨r,semantic1,_,run⟩ := pair_bind_success _ _ _ run
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,bind_tc_ok] at run
    simp only [bind_assoc_eq] at run
    obtain ⟨err,_,run⟩ := bind_success _ _ _ run
    cases run
  | Ok unit =>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
   obtain ⟨off1,_,run⟩ := bind_success _ _ _ run
   obtain ⟨input1,_,run⟩ := bind_success _ _ _ run
   obtain ⟨r,y11,_,run⟩ := pair_bind_success _ _ _ run
   cases r with
   | Err e =>
     simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,bind_tc_ok] at run
     simp only [bind_assoc_eq] at run
     obtain ⟨err,_,run⟩ := bind_success _ _ _ run
     cases run
   | Ok unit =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
    obtain ⟨semantic2,_,run⟩ := bind_success _ _ _ run
    obtain ⟨y12,_,run⟩ := bind_success _ _ _ run
    obtain ⟨r,hview,run⟩ := bind_success _ _ _ run
    cases r with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
       core.convert.FromSame.from,bind_tc_ok] at run
      cases run
    | Ok v =>
     simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
     obtain ⟨verified,_,run⟩ := bind_success _ _ _ run
     obtain ⟨r,_,run⟩ := bind_success _ _ _ run
     cases r with
     | Err e =>
       simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at run
       cases run
     | Ok sem =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      obtain ⟨marked,_,run⟩ := bind_success _ _ _ run
      exact ⟨semantic2,y12,v,sem,hview,run⟩
#print axioms source
end XSe_PrepareCuts
