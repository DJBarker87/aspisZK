-- PCVN_ item (1) op17 (weights::powers): the fresh 4bb3b3f emission text (PRVFresh_LoopPowersEarlySteps, overflow ON; the p2d file dropped it because
-- the gate universe has no aspis_core.* names) against the gate AspisR1LoopPowers.weights.early_powers, with the three aspis-core callees
-- (WideExact.ZERO, ONE, mul) bound to the gate constants field.WideExact.ZERO/ONE/mul. That binding is CONDITIONAL_ON_BINDING and is stated, not hidden.
import Aeneas
import LoopPowersEarlyTotal
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace AspisR1LoopPowers
namespace PCVN_FreshPowers
abbrev W := field.WideExact

/-- fresh text of weights::powers loop body (aspis_core.field.wide_exact.WideExact.mul bound to field.WideExact.mul) -/
def powers_loop.body {N : Std.Usize} (x : W) (out : Array W N) (p : W) (i : Std.Usize) :
  Result (ControlFlow ((Array W N) × W × Std.Usize) ((Array W N) × (Option (Array W N)))) := do
  if i < N
  then
    let (_, index_mut_back) ← Array.index_mut_usize out i
    let i1 ← i + 1#usize
    if i1 = N
    then let out1 := index_mut_back p
         ok (done (out1, some out1))
    else
      let p1 ← field.WideExact.mul p x
      let out1 := index_mut_back p
      ok (cont (out1, p1, i1))
  else ok (done (out, none))

def powers_loop {N : Std.Usize} (x : W) (out : Array W N) (p : W) (i : Std.Usize) :
  Result ((Array W N) × (Option (Array W N))) := do
  loop (fun (out1, p1, i1) => powers_loop.body x out1 p1 i1) (out, p, i)

def powers (N : Std.Usize) (x : W) : Result (Array W N) := do
  let we ← ok field.WideExact.ZERO
  let out := Array.repeat N we
  let p ← ok field.WideExact.ONE
  let (out1, pending_return) ← powers_loop x out p 0#usize
  match pending_return with
  | none => ok out1
  | some out2 => ok out2
end PCVN_FreshPowers

namespace PCVN_Op17
open PCVN_FreshPowers

theorem loop_unfold {α β : Type _} (body : α → Result (ControlFlow α β)) (x : α) :
    loop body x = (match body x with
      | ok r => (match r with | ControlFlow.cont x' => loop body x' | ControlFlow.done y => ok y)
      | fail e => fail e
      | div => div) := by
  rw [loop]; rfl

theorem post_eq {N : Std.Usize} (x : W) :
    ∀ (k : Nat) (out : Array W N) (p : W) (i : Std.Usize), N.val - i.val = k →
      (do let (o, pend) ← powers_loop x out p i
          ok (match pend with | none => o | some o2 => o2)) = weights.early_powers_loop x out p i := by
  intro k
  induction k with
  | zero =>
    intro out p i hk
    have hi : ¬ (i < N) := by
      intro h; have := (Aeneas.Std.UScalar.lt_equiv i N).mp h; omega
    unfold powers_loop weights.early_powers_loop
    rw [loop_unfold, loop_unfold]
    simp [powers_loop.body, weights.early_powers_loop.body, hi]
  | succ k ih =>
    intro out p i hk
    by_cases hi : i < N
    · have hmax : i.val + (1#usize).val ≤ Usize.max := by scalar_tac
      obtain ⟨i1, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) hmax)
      have hk' : N.val - i1.val = k := by scalar_tac
      unfold powers_loop weights.early_powers_loop
      rw [loop_unfold, loop_unfold]
      simp only [powers_loop.body, weights.early_powers_loop.body, hi, if_true, hz]
      cases hm : Array.index_mut_usize out i with
      | fail e => simp [hm]
      | div => simp [hm]
      | ok r =>
        obtain ⟨v, back⟩ := r
        simp only [hm, bind_tc_ok]
        by_cases he : i1 = N
        · simp [he]
        · cases hmul : field.WideExact.mul p x with
          | fail e => simp [he, hmul]
          | div => simp [he, hmul]
          | ok p1 =>
            simp only [he, hmul, if_false, bind_tc_ok]
            exact ih (back p) p1 i1 hk'
    · unfold powers_loop weights.early_powers_loop
      rw [loop_unfold, loop_unfold]
      simp [powers_loop.body, weights.early_powers_loop.body, hi]
end PCVN_Op17
end AspisR1LoopPowers
