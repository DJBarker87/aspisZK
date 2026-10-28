import NBD_DigestTrace
set_option autoImplicit false
namespace NBD_DigestNativeStep
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1TerminalDecoder NBD_DigestTrace

/-- Exact observable tuple checked by NBD_K006, with the next loop test summarized. -/
def step (w : Nat → Nat) (i : Nat) : Bool × Nat × Bool :=
  if i < 8 then
    if 2147483647 ≤ w i then (false,i,true)
    else (true,i+1,decide (i+1=8))
  else (true,i,true)

def observe (i : Usize) : ControlFlow Usize Bool → Bool × Nat × Bool
  | .done b => (b,i.val,true)
  | .cont next => (true,next.val,decide (next.val=8))

def projected (d : Array U32 8#usize) (i : Usize) : Result (Bool × Nat × Bool) := do
  let out ← pool_v1.pair_tree_profile.digest_is_canonical_loop.body d i
  ok (observe i out)

/-- The probe's summarized native one-step result is the emitted scanner's result. -/
theorem source (d : Array U32 8#usize) (i : Usize) (hi : i.val ≤ 8) :
    projected d i = ok (step (word d) i.val) := by
  have spec : projected d i ⦃ out => out = step (word d) i.val ⦄ := by
    unfold projected pool_v1.pair_tree_profile.digest_is_canonical_loop.body
    step*
    all_goals try unfold aspis_core.field.P at *
    all_goals simp_all [observe, step, word]
    all_goals scalar_tac
  obtain ⟨out,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

/-- All three native branches fit the induction, including the final successful limb. -/
theorem compose (w : Nat → Nat) (i : Nat) (hi : i ≤ 8) (b : Bool)
    (rest : ∀ next, step w i = (true,next,false) → Trace w next (8-next) b)
    (terminal : ∀ value next, step w i = (value,next,true) → value = b) :
    Trace w i (8-i) b := by
  by_cases done : i = 8
  · subst i
    have hb := terminal true 8 (by simp [step])
    rw [←hb]
    exact .done 8
  · have hlt : i < 8 := by omega
    by_cases bad : 2147483647 ≤ w i
    · have hb := terminal false i (by simp [step,hlt,bad])
      rw [←hb]
      have hn : 8-i = (7-i)+1 := by omega
      rw [hn]
      exact .reject i (7-i) bad
    · have good : w i < 2147483647 := by omega
      have hn : 8-i = (7-i)+1 := by omega
      rw [hn]
      by_cases last : i+1=8
      · have hb := terminal true (i+1) (by simp [step,hlt,bad,last])
        rw [←hb]
        apply Trace.advance i (7-i) true good
        have hzero : 7-i=0 := by omega
        rw [hzero]
        exact .done (i+1)
      · have tail := rest (i+1) (by simp [step,hlt,bad,last])
        apply Trace.advance i (7-i) b good
        simpa only [show 8-(i+1)=7-i by omega] using tail

#print axioms source
#print axioms compose
end NBD_DigestNativeStep
