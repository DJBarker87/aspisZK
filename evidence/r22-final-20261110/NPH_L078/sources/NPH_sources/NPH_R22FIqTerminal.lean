import NLU_TerminalCanonical
import NHU_TransitionTotal

/-! NPH_ (R22, FIq step 1): the retained terminal never fails on its input domain.
`terminal_total`: on NLU_Terminal.InputDomain pub c (public digest domain, asset_id < P, canonical
challenges) with canonical claims and alpha, FIq_Terminal.terminal pub claims alpha c = ok out for
some out (an Ok value or an Err rejection; never Aeneas fail or div). So every checked FIq
operation executed inside the terminal (every FIq kernel call of the pair-forest semantic
terminal, the copy terminal and the state-only Poseidon oracle) returned ok.
Composition (closure theorems at the SAME arguments, no new premise):
- amount precheck: NLH_TermAmount.rejected (invalid amount: ok Err) / NLH_CompRoot.factor_good;
- validate_transition: NHU_TransitionTotal.result (ok for EVERY public), the only child that
  NLH_CompRoot.source leaves with a fail/div branch;
- the composition tail (gathers, selectors, Poseidon selectors, Poseidon oracle, semantic
  absorption, h1, variant, copy terminal, prepared products, 28 Horner steps, g):
  NLH_CompTailFold.source, which returns ok (Ok final) with canonical composition/h/active;
- the terminal arithmetic suffix: NKR_TermTail.result;
- the 84-cell gather, the semantic public and the map/map_err arms: NLH_TermWrapperFactor.source.
Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22FIqTerminal
open Aeneas Aeneas.Std Result

section core
open FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem composition_ok (pub : NKI_InitialPrefix.Public) (claims : Array NQ 84#usize)
    (point : Array NQ 10#usize) (lambda chi theta : NQ) (hd : NKR_DigestChildren.Domain pub)
    (hc : canonical claims) (hp : canonical point) (hl : Canon lambda) (hchi : Canon chi)
    (ht : Canon theta) (asset : pub.asset_id.val < 2147483647) :
    ∃ v, composition_parts pub claims point lambda chi theta = ok v ∧
      ∀ child, v = .Ok child → Canon child.1 ∧ Canon child.2.2.2.2.1 ∧ Canon child.2.2.2.2.2 := by
  cases bad : NLH_TermAmount.invalid pub.withdrawal_amount with
  | true =>
    exact ⟨_, NLH_TermAmount.rejected pub claims point lambda chi theta bad, fun child h => by cases h⟩
  | false =>
    rw [NLH_CompRoot.factor_good pub claims point lambda chi theta bad]
    obtain ⟨status, hv⟩ := NHU_TransitionTotal.result pub
    rw [hv, bind_tc_ok]
    cases status with
    | Err e => exact ⟨_, rfl, fun child h => by cases h⟩
    | Ok u =>
      obtain ⟨final, _, tailCall, cc, _, _, _, ch, ca⟩ := NLH_CompTailFold.source pub claims point
        lambda chi theta NLH_CompRun.initial hd hc hp hl hchi ht asset (NLH_TermAmount.canonical pub bad)
      refine ⟨_, tailCall, fun child h => ?_⟩
      injection h with h
      subst h
      exact ⟨cc, ch, ca⟩
#print axioms composition_ok

theorem parts_ok (pub : NKI_InitialPrefix.Public) (claims : Array NQ 84#usize)
    (point zc : Array NQ 10#usize) (lambda chi theta mu : NQ) (hd : NKR_DigestChildren.Domain pub)
    (hc : canonical claims) (hp : canonical point) (hz : canonical zc) (hl : Canon lambda)
    (hchi : Canon chi) (ht : Canon theta) (hm : Canon mu) (asset : pub.asset_id.val < 2147483647) :
    ∃ v, terminal_parts pub claims point lambda chi theta zc mu = ok v := by
  obtain ⟨v, hv, hcan⟩ := composition_ok pub claims point lambda chi theta hd hc hp hl hchi ht asset
  rw [NLH_TermPartsFactor.source]
  unfold NLH_TermPartsFactor.reference
  rw [hv, bind_tc_ok]
  cases v with
  | Err e => exact ⟨_, rfl⟩
  | Ok child =>
    obtain ⟨cc, ch, ca⟩ := hcan child rfl
    obtain ⟨calls, arith, _, _⟩ := NKR_TermTail.result zc point mu child.1 child.2.2.2.2.1
      child.2.2.2.2.2 hz hp hm cc ch ca
    refine ⟨.Ok (calls.out, child.2.1, child.2.2.1, child.2.2.2.1), ?_⟩
    (simp only [NKR_TermTail.after, NKR_TermTail.tail, arith, bind_tc_ok]) <;> rfl
#print axioms parts_ok

theorem qm31_ok (pub : r0.Public) (claims : NLH_TermSelected.Claims) (point : Array NQ 10#usize)
    (c : state_only_prefix.r0.Challenges)
    (hd : NKR_DigestChildren.Domain (NKR_TermPublic.value pub)) (hc : ∀ row ∈ claims.val, canonical row)
    (hp : canonical point) (hz : canonical c.zc) (hl : Canon c.lambda) (hchi : Canon c.chi)
    (ht : Canon c.theta) (hm : Canon c.mu)
    (asset : (NKR_TermPublic.value pub).asset_id.val < 2147483647) :
    ∃ v, r0.Public.terminal_qm31 pub claims point c = ok v := by
  obtain ⟨selected, _, cs, eq⟩ := NLH_TermWrapperFactor.source pub claims point c hc
  rw [eq]
  unfold NLH_TermWrapperFactor.reference
  obtain ⟨v, hv⟩ := parts_ok (NKR_TermPublic.value pub) selected point c.zc c.lambda c.chi c.theta
    c.mu hd cs hp hz hl hchi ht hm asset
  rw [hv, bind_tc_ok]
  cases v with
  | Ok parts => exact ⟨_, rfl⟩
  | Err e => exact ⟨_, rfl⟩
#print axioms qm31_ok
end core

section deployed
open AspisR1PublicPreparation FIq_Carriers

/-- The retained terminal is ok (never fail/div) on its input domain with canonical claims and alpha. -/
theorem terminal_total (pub : Public) (claims : NLC_Finish.Claims) (alpha : NLC_Finish.Alpha)
    (c : r1_wire.Challenges) (domain : NLU_Terminal.InputDomain pub c)
    (hc : ∀ row ∈ (mapArray (mapArray toQ) claims).val, FIw_ArrayValue.canonical row)
    (ha : FIw_ArrayValue.canonical (mapArray toQ alpha)) :
    ∃ out, FIq_Terminal.terminal pub claims alpha c = ok out := by
  obtain ⟨v, hv⟩ := qm31_ok (toPublic pub) (mapArray (mapArray toQ) claims) (mapArray toQ alpha)
    (toChallenges c) domain.digest hc ha domain.zc domain.lambda domain.chi domain.theta domain.mu
    domain.asset
  unfold FIq_Terminal.terminal
  rw [hv, bind_tc_ok]
  cases v with
  | Ok q => exact ⟨_, rfl⟩
  | Err e => exact ⟨_, rfl⟩
#print axioms terminal_total

/-- The deployed finish boundary's terminal slot is FIq_Terminal.terminal. -/
theorem deployed_terminal (r : NP6_StdModel.Reservation) :
    (IDa_Deployed.boundaries r).terminal = FIq_Terminal.terminal := rfl
#print axioms deployed_terminal
end deployed

end AspisR1.NPH_R22FIqTerminal
