import Std

/-! Finite coupling, at the event-count level. For a nonempty equiprobable
sample list, divide both sides by its length to obtain the event probability
bound. No source coupling, uniformity or cost premise is manufactured here.
The joint observation contains the published view AND all leaf trace inputs.
In particular this theorem cannot be applied to separate marginal laws. -/
set_option autoImplicit false
namespace R1Z.L2Leaf_JointCount

/-- Multiplicity is intentional: this is a list of equally likely samples. -/
def hits {Sample : Type} (test : Sample → Bool) : List Sample → Nat
  | [] => 0
  | s::ss => (if test s then 1 else 0) + hits test ss

/-- Generic finite coupling bound, with the bad event counted once. -/
theorem count_le_bad {Sample View : Type} (samples : List Sample)
    (real ideal : Sample → View) (bad : Sample → Bool)
    (agree : ∀ s, bad s = false → real s = ideal s) (test : View → Bool) :
    hits (fun s => test (real s)) samples ≤
      hits (fun s => test (ideal s)) samples + hits bad samples := by
  induction samples with
  | nil => exact Nat.le_refl 0
  | cons s ss ih =>
    cases hb : bad s with
    | false =>
      have same := congrArg test (agree s hb)
      simp only [hits,hb,Bool.false_eq_true,ite_false,same]
      omega
    | true =>
      simp only [hits,hb,ite_true]
      split <;> split <;> omega

/-- Trace postprocessing and the published view share ONE coupling and ONE
exceptional set. Input agreement is stronger than published-view agreement;
it must be established on actual real/ideal runs, including rejected attempts. -/
theorem joint_trace_count_bound {Sample View Input Trace : Type}
    (samples : List Sample) (realView idealView : Sample → View)
    (realInput idealInput : Sample → Input) (observe : Input → Trace)
    (bad : Sample → Bool)
    (viewAgree : ∀ s, bad s = false → realView s = idealView s)
    (inputAgree : ∀ s, bad s = false → realInput s = idealInput s)
    (test : View × Trace → Bool) :
    hits (fun s => test (realView s,observe (realInput s))) samples ≤
      hits (fun s => test (idealView s,observe (idealInput s))) samples + hits bad samples ∧
    hits (fun s => test (idealView s,observe (idealInput s))) samples ≤
      hits (fun s => test (realView s,observe (realInput s))) samples + hits bad samples := by
  have same (s : Sample) (hs : bad s = false) :
      (realView s,observe (realInput s)) = (idealView s,observe (idealInput s)) := by
    rw [viewAgree s hs,inputAgree s hs]
  exact ⟨count_le_bad samples _ _ bad same test,
    count_le_bad samples _ _ bad (fun s hs => (same s hs).symm) test⟩

/-- With no bad samples the complete joint event counts agree exactly. -/
theorem joint_trace_count_exact {Sample View Input Trace : Type}
    (samples : List Sample) (realView idealView : Sample → View)
    (realInput idealInput : Sample → Input) (observe : Input → Trace)
    (viewAgree : ∀ s, realView s = idealView s)
    (inputAgree : ∀ s, realInput s = idealInput s)
    (test : View × Trace → Bool) :
    hits (fun s => test (realView s,observe (realInput s))) samples =
      hits (fun s => test (idealView s,observe (idealInput s))) samples := by
  congr 1
  funext s
  rw [viewAgree s,inputAgree s]

/-- An L1 seed relabeling can preserve a verdict while changing its L2
trace. This prevents an invalid use of count_history_preserved as inputAgree. -/
theorem projection_agreement_not_joint_agreement :
    ∃ a b : Bool × Nat, a.1 = b.1 ∧ a ≠ b := by
  exact ⟨(true,0),(true,1),rfl,by decide⟩

#print axioms count_le_bad
#print axioms joint_trace_count_bound
#print axioms joint_trace_count_exact
#print axioms projection_agreement_not_joint_agreement
end R1Z.L2Leaf_JointCount
