import R1Z.ProverRwSuccessInverseSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessPowerTotal
open Aeneas Aeneas.Std Result ControlFlow
namespace S
abbrev mul := ProverRwSuccessInverseSource.field.M31.mul
abbrev body := ProverRwSuccessInverseSource.field.M31.pow_loop.body
abbrev pow := ProverRwSuccessInverseSource.field.M31.pow_loop
end S

theorem mul_total (a b : U32) : ∃ c, S.mul a b = .ok c := by
  simp only [S.mul,ProverRwSuccessInverseSource.field.M31.mul,
    AspisR1ProducerRelease47.field.M31.mul,AspisR1ProducerRelease47.field.reduce_u64,
    lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩

theorem shift (e : U64) : (U64.wrapping_shr e 1#u32).val = e.val/2 := rfl

theorem loop_bind {A B : Type} (step : A → Result (ControlFlow A B)) (a : A) :
    loop step a = (do
      let cf ← step a
      match cf with
      | .cont next => loop step next
      | .done out => .ok out) := by
  rw [loop]
  cases step a <;> rfl

theorem pow_unfold (exp : U64) (base acc : U32) :
    S.pow exp base acc = (do
      let cf ← S.body exp base acc
      match cf with
      | .done x => .ok x
      | .cont (e,b,a) => S.pow e b a) := by
  unfold S.pow ProverRwSuccessInverseSource.field.M31.pow_loop
  rw [ProverRwSuccessPowerTotal.loop_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro cf _
  cases cf with
  | done x => rfl
  | cont next => rcases next with ⟨e,b,a⟩; rfl

/-- Full U64 exponent range, arbitrary raw base/accumulator. No unrolling of
P-2 or success premise: the machine shift strictly reduces the exponent. -/
theorem pow_total (exp : U64) (base acc : U32) : ∃ c, S.pow exp base acc = .ok c := by
  generalize he : exp.val = n
  induction n using Nat.strong_induction_on generalizing exp base acc with
  | h n ih =>
    rw [pow_unfold]
    unfold S.body ProverRwSuccessInverseSource.field.M31.pow_loop.body
    by_cases hz : exp > 0#u64
    · rw [if_pos hz]
      obtain ⟨square,hs⟩ := mul_total base base
      have small : (U64.wrapping_shr exp 1#u32).val < n := by
        rw [shift]
        have pos : 0 < exp.val := by change (0#u64).val < exp.val at hz; exact hz
        omega
      by_cases bit : exp &&& 1#u64 = 1#u64
      · obtain ⟨next,hn⟩ := mul_total acc base
        obtain ⟨out,ho⟩ := ih _ small (U64.wrapping_shr exp 1#u32) square next rfl
        refine ⟨out,?_⟩
        simpa only [lift,bind_tc_ok,bit,if_true,hn,hs] using ho
      · obtain ⟨out,ho⟩ := ih _ small (U64.wrapping_shr exp 1#u32) square acc rfl
        refine ⟨out,?_⟩
        simpa only [lift,bind_tc_ok,bit,if_false,hs] using ho
    · rw [if_neg hz]
      exact ⟨acc,rfl⟩
#print axioms mul_total
#print axioms shift
#print axioms loop_bind
#print axioms pow_unfold
#print axioms pow_total
end R1Z.ProverRwSuccessPowerTotal
