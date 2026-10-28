import R1Z.ProverRw18ContextBranch
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ContextInduction
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw18InlineContext
variable [ExternalTypes] [ExternalFuns]

def step (lambda : Q) (value : U32) (state : Q × Q) : Result (Q × Q) :=
  PV_RW_CompressEmission.generated.shipped_step state.1 state.2 value lambda

-- This is induction on the number of remaining iterator elements, not
-- normalization of a concrete arity-16 execution. Primitive failure and
-- divergence remain in Result on both sides.
theorem run (lambda : Q) (values : Slice U32) (i : Nat) (out power : Q) :
    ProverRw18InlineContext.run lambda (⟨values,i⟩ : Iter) out power = (do
      let final ← PV_RW_NativeForSource.run (step lambda) (⟨values,i⟩ : Iter) (out,power)
      ok final.1) := by
  generalize hn : values.val.length-i = n
  induction n using Nat.strong_induction_on generalizing i out power with
  | h n ih =>
    by_cases active : i < values.val.length
    · rw [ProverRw18ContextBranch.some lambda values i active,
        PV_RW_NativeForSource.run_some (step lambda) values i active]
      have smaller : values.val.length-(i+1)<n := by omega
      simp only [step,PV_RW_CompressEmission.generated.shipped_step,bind_assoc_eq,bind_tc_ok]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro scaled _
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro out1 _
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro power1 _
      exact ih _ smaller (i+1) out1 power1 rfl
    · rw [ProverRw18ContextBranch.none lambda values i (by omega),
        PV_RW_NativeForSource.run_none (step lambda) values i (by omega)]
      rfl

#print axioms run
end R1Z.ProverRw18ContextInduction
