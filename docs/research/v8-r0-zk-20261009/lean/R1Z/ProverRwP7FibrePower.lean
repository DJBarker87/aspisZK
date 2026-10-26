import R1Z.ProverRwP7FibreArithmetic
import R1Z.ProverRwSuccessPowerTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7FibrePower
open Aeneas Aeneas.Std Result ControlFlow ProverRwP7FibreArithmetic
abbrev Src := ProverRwP7FibreSource.aspis_core.field.CM31.pow_loop
abbrev Body := ProverRwP7FibreSource.aspis_core.field.CM31.pow_loop.body

theorem unfold_source (exp : U64) (base acc : C) :
    Src exp base acc = (do
      let cf ← Body exp base acc
      match cf with
      | .done x => ok x
      | .cont (e,b,a) => Src e b a) := by
  unfold Src ProverRwP7FibreSource.aspis_core.field.CM31.pow_loop
  rw [ProverRwSuccessPowerTotal.loop_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro cf _
  cases cf with
  | done x => rfl
  | cont p => rcases p with ⟨e,b,a⟩; rfl

theorem total (exp : U64) (base acc : C) : ∃ out, Src exp base acc = ok out := by
  generalize he : exp.val = n
  induction n using Nat.strong_induction_on generalizing exp base acc with
  | h n ih =>
    rw [unfold_source]
    unfold Body ProverRwP7FibreSource.aspis_core.field.CM31.pow_loop.body
    by_cases hz : exp>0#u64
    · rw [if_pos hz]
      obtain ⟨sq,hsq⟩ := square_total base
      have small : (U64.wrapping_shr exp 1#u32).val < n := by
        change exp.val/2<n
        have pos : 0<exp.val := hz
        omega
      by_cases bit : exp &&& 1#u64 = 1#u64
      · obtain ⟨next,hn⟩ := mul_total acc base
        obtain ⟨out,ho⟩ := ih _ small (U64.wrapping_shr exp 1#u32) sq next rfl
        refine ⟨out,?_⟩
        simpa only [lift,bind_tc_ok,bit,if_true,hn,hsq] using ho
      · obtain ⟨out,ho⟩ := ih _ small (U64.wrapping_shr exp 1#u32) sq acc rfl
        refine ⟨out,?_⟩
        simpa only [lift,bind_tc_ok,bit,if_false,hsq] using ho
    · rw [if_neg hz]
      exact ⟨acc,rfl⟩
#print axioms unfold_source
#print axioms total
end R1Z.ProverRwP7FibrePower
