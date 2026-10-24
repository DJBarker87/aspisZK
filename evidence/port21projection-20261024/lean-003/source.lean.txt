import OracleProgramLawExt

/-! Synchronous oracle simulation with a terminal relation. Neither private
state equality nor equality of whole programs is a premise. This is a
composition rule, not an implementation of native allocator primitives. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port21PROJECTION_Core
open FS
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8PairedCommitment
variable {I A N M : Type}

/-- Every oracle answer branch is retained, including branches terminating in
error or abort. Native silent/private steps must be discharged by the source
interpretation before constructing this relation. -/
inductive Sim (R : N → M → Prop) : Program I A N → Program I A M → Prop where
  | done (n : N) (m : M) : R n m → Sim R (.done n) (.done m)
  | ask (i : I) (n : A → Program I A N) (m : A → Program I A M) :
      (∀ a, Sim R (n a) (m a)) → Sim R (.ask i n) (.ask i m)

theorem evaluated {R : N → M → Prop} {n : Program I A N} {m : Program I A M}
    (h : Sim R n m) (H : I → A) :
    (eval H n).1 = (eval H m).1 ∧ R (eval H n).2 (eval H m).2 := by
  induction h with
  | done n m related => exact ⟨rfl,related⟩
  | ask i n m related ih =>
    obtain ⟨logs,values⟩ := ih (H i)
    exact ⟨congrArg (List.cons (i,H i)) logs,values⟩

/-- Any charge of the full ordered log, including duplicate or rejected-prefix
charges, transports. This is stronger than accepted-run query accounting. -/
theorem charge {R : N → M → Prop} {n : Program I A N} {m : Program I A M}
    (h : Sim R n m) (H : I → A) (cost : List (I × A) → Nat) :
    cost (eval H n).1 = cost (eval H m).1 :=
  congrArg cost (evaluated h H).1

/-- Adaptive continuations may differ and inspect their respective carriers;
they must preserve the explicitly stated terminal relation. -/
theorem bind_sim {R : N → M → Prop} {n : Program I A N} {m : Program I A M}
    {N' M' : Type} {S : N' → M' → Prop}
    (h : Sim R n m) (kn : N → Program I A N') (km : M → Program I A M')
    (next : ∀ n m, R n m → Sim S (kn n) (km m)) :
    Sim S (bind n kn) (bind m km) := by
  induction h with
  | done n m related => exact next n m related
  | ask i n m related ih => exact .ask i _ _ ih

/-- This law uses the actual memoized oracle probability semantics over an
arbitrary address type; no uniform infinite oracle distribution is assumed. -/
theorem mass_le [DecidableEq I] [Fintype A] [Inhabited A]
    {R : N → M → Prop} {n : Program I A N} {m : Program I A M}
    (h : Sim R n m) (fn : View I A N → ℚ) (fm : View I A M → ℚ)
    (leaf : ∀ log n m, R n m → fn (log,n) ≤ fm (log,m)) :
    lazyMean n emptyTable fn ≤ lazyMean m emptyTable fm := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  obtain ⟨logs,values⟩ := evaluated h H
  have result := leaf (eval H n).1 (eval H n).2 (eval H m).2 values
  change fn ((eval H n).1,(eval H n).2) ≤ fm ((eval H m).1,(eval H m).2)
  rw [← logs]
  exact result

#print axioms evaluated
#print axioms charge
#print axioms bind_sim
#print axioms mass_le
end AspisR1.Port21PROJECTION_Core
end
