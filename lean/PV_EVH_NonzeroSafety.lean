import PV_EVH_NonzeroFlow
import PV_EVH_LiftLaws
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NonzeroSafety
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
open ControlFlow
variable [ExternalTypes] [ExternalFuns]

/-- The active source branch supplies exactly the checked index's bound. -/
theorem array_read (bytes : Array U8 32#usize) (i : Usize) (bound : i < 32#usize) :
    ∃ value, Array.index_usize bytes i = .ok value := by
  obtain ⟨value,read,same⟩ := WP.spec_imp_exists
    (Array.index_usize_spec bytes i (by
      change i.val < bytes.val.length
      rw [bytes.property]
      exact bound))
  exact ⟨value,read⟩

theorem increment (i : Usize) (bound : i < 32#usize) :
    (Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  rw [Usize.wrapping_add_val_eq]
  change (i.val+1) % UScalar.size .Usize = i.val+1
  apply Nat.mod_eq_of_lt
  have hsize := (32#usize).hSize
  change i.val < (32#usize).val at bound
  omega

/-- An equality proved from the interpreted body, rather than using a whole
helper Result to define its execution. Only checked value primitives occur. -/
theorem step_plain (bytes : Array U8 32#usize) (combined : U8) (i : Usize) :
    PV_EVH_NonzeroStep.run bytes combined i {} =
      PV_EVH_Prefix.lift
        (aspis_prover.state_only_entropy.entropy_nonzero32_loop.body bytes combined i) := by
  unfold PV_EVH_NonzeroStep.run
    aspis_prover.state_only_entropy.entropy_nonzero32_loop.body
  by_cases h : i < 32#usize
  · simp only [h,if_true]
    simp only [PV_EVH_LiftLaws.bind_lift]
  · simp only [h,if_false]

theorem step_total (bytes : Array U8 32#usize) (combined : U8) (i : Usize) :
    ∃ cf, aspis_prover.state_only_entropy.entropy_nonzero32_loop.body bytes combined i = .ok cf := by
  by_cases h : i < 32#usize
  · obtain ⟨value,read⟩ := array_read bytes i h
    refine ⟨.cont (combined ||| value,Usize.wrapping_add i 1#usize),?_⟩
    simp only [aspis_prover.state_only_entropy.entropy_nonzero32_loop.body,h,if_true,read,
      bind_tc_ok,Aeneas.Std.lift]
  · refine ⟨.done combined,?_⟩
    simp only [aspis_prover.state_only_entropy.entropy_nonzero32_loop.body,h,if_false]
#print axioms array_read
#print axioms increment
#print axioms step_plain
#print axioms step_total
end PV_EVH_NonzeroSafety
