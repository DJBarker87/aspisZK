import R1Z.ProverCommitFuelJoin22
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublicFailureOption
open R0Z R0Z.FsAbort R0Z.FsGood

/-- Candidate model statement B. The environment supplies the same public
signal to both experiments. `none` runs the unchanged experiment; `some e`
returns its complete public failure view. The failure view may include bytes,
side channels and oracle history; it has no witness argument. Not adopted. -/
def experiment {E W R V : Type} (failure : E → V) (success : W → R → V)
    (signal : Option E) (w : W) (r : R) : V :=
  match signal with
  | none => success w r
  | some e => failure e

theorem failure_views_agree {E W R I V : Type} (failure : E → V)
    (real : W → R → V) (simEideal : I → V)
    (e : E) (w : W) (r : R) (i : I) :
    experiment failure real (some e) w r =
      experiment failure (fun _ : Unit => simEideal) (some e) () i := rfl

theorem failure_witness_independent {E W R V : Type} (failure : E → V)
    (real : W → R → V) (e : E) (w u : W) (r t : R) :
    experiment failure real (some e) w r = experiment failure real (some e) u t := rfl

/-- For EACH fixed public signal, the old bound and complete observer are
preserved. The existing simE-ideal function is passed intact. This theorem
does not establish the native environment's witness independence. -/
theorem bound_unchanged {E W R I V : Type} [Fintype R] [Nonempty R]
    [Fintype I] [Nonempty I]
    (failure : E → V) (real : W → R → V) (simEideal : I → V)
    (test : V → ℚ) (epsilon : ℚ) (nonnegative : 0 ≤ epsilon)
    (old_bound : ∀ w, |mean (fun r => test (real w r)) -
      mean (fun i => test (simEideal i))| ≤ epsilon)
    (signal : Option E) (w : W) :
    |mean (fun r => test (experiment failure real signal w r)) -
      mean (fun i => test (experiment failure (fun _ : Unit => simEideal) signal () i))| ≤
      epsilon := by
  cases signal with
  | none => exact old_bound w
  | some e =>
    simp only [experiment,mean_const,sub_self,abs_zero]
    exact nonnegative

#print axioms failure_views_agree
#print axioms failure_witness_independent
#print axioms bound_unchanged
end R1Z.PV_RunJoin_PublicFailureOption
