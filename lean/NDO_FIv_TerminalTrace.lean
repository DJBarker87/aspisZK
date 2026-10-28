import RPu_FIq_Native14
import RPu_FIv_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_TerminalTrace
open Aeneas Aeneas.Std Result
open FIq_Native
abbrev NQ := field.QM31
abbrev SemPub := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev parts := pool_v1.pair_forest_semantic_terminal.terminal_parts
abbrev composition := pool_v1.pair_forest_semantic_terminal.composition_parts

structure Calls (left right : Array NQ 10#usize) (mu comp h active out : NQ) where
  eq : NQ
  weighted : NQ
  muH : NQ
  sum : NQ
  mu2 : NQ
  inactive : NQ
  inactiveH : NQ
  extra : NQ
  equality : pool_v1.pair_forest_semantic_terminal.equality_value left right=ok eq
  weight : field.QM31.mul eq comp=ok weighted
  mu_h : field.QM31.mul mu h=ok muH
  sum_call : field.QM31.add weighted muH=ok sum
  mu_square : field.QM31.mul mu mu=ok mu2
  inactive_call : field.QM31.sub field.QM31.ONE active=ok inactive
  inactive_h : field.QM31.mul inactive h=ok inactiveH
  extra_call : field.QM31.mul mu2 inactiveH=ok extra
  returned : field.QM31.add sum extra=ok out

theorem reached (pub : SemPub) (claims : Array NQ 84#usize)
    (point zc : Array NQ 10#usize) (lambda chi theta mu out : NQ)
    (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize) (g : NQ)
    (success : parts pub claims point lambda chi theta zc mu=ok (.Ok (out,c1,mask,g))) :
    ∃ comp h active,
      composition pub claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active)) ∧
      Nonempty (Calls zc point mu comp h active out) := by
  unfold parts pool_v1.pair_forest_semantic_terminal.terminal_parts at success
  obtain ⟨r,called,success⟩ := FIv_Map.bind_success _ _ _ success
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,bind_tc_ok] at success
    cases success
  | Ok tuple =>
    rcases tuple with ⟨comp,c1',mask',g',h,active⟩
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at success
    obtain ⟨eq,heq,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨weighted,hw,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨muH,hmh,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨sum,hs,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨mu2,hm2,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨inactive,hi,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨inactiveH,hih,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨extra,he,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨original,ho,success⟩ := FIv_Map.bind_success _ _ _ success
    have same := core.result.Result.Ok.inj (Result.ok.inj success)
    cases same
    exact ⟨comp,h,active,called,⟨⟨eq,weighted,muH,sum,mu2,inactive,inactiveH,extra,
      heq,hw,hmh,hs,hm2,hi,hih,he,ho⟩⟩⟩

#print axioms reached
end AspisR1.FIv_TerminalTrace
end
