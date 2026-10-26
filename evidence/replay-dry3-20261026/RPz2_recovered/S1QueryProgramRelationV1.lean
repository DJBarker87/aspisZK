import S1QueryPairEvaluationV1
import AspisV8R19.AdaptiveFirstReadLaw
set_option autoImplicit false
noncomputable section
namespace AspisS1QueryProgramRelation
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation.PreparedHashCode.QueryPair

/-- Structural same-ask relation: ALL reply branches, including inconsistent
answers at repeated addresses. The terminal relation may be accepted-only. -/
inductive SameReads {I Answer A B : Type} (R : A → B → Prop) :
    Program I Answer A → Program I Answer B → Prop where
  | done {a : A} {b : B} (related : R a b) : SameReads R (.done a) (.done b)
  | ask (i : I) {f : Answer → Program I Answer A} {g : Answer → Program I Answer B}
      (next : ∀ reply,SameReads R (f reply) (g reply)) : SameReads R (.ask i f) (.ask i g)

theorem paired_related {A B : Type} (R : A → B → Prop)
    (first : List State → List State → A) (second : List State → List State → B)
    (n : Nat) (state : State) (blocks advances : List State)
    (terminal : ∀ bs xs,bs.length=blocks.length+n → xs.length=advances.length+n → R (first bs xs) (second bs xs)) :
    SameReads R (pairedBytesProgram first n state blocks advances)
      (pairedBytesProgram second n state blocks advances) := by
  induction n generalizing state blocks advances with
  | zero => exact .done (terminal blocks advances (by omega) (by omega))
  | succ n ih =>
    apply SameReads.ask
    intro block
    apply SameReads.ask
    intro advance
    apply ih
    intro bs xs hbs hxs
    apply terminal bs xs
    · simp only [List.length_append,List.length_singleton] at hbs; omega
    · simp only [List.length_append,List.length_singleton] at hxs; omega

/-- Exact ordered trace and terminal relation for arbitrary functional oracles. -/
theorem SameReads.eval_related {I Answer A B : Type} {R : A → B → Prop}
    {p : Program I Answer A} {q : Program I Answer B} (h : SameReads R p q) (oracle : I → Answer) :
    (eval oracle p).1=(eval oracle q).1 ∧ R (eval oracle p).2 (eval oracle q).2 := by
  induction h with
  | done related => exact ⟨rfl,related⟩
  | ask i next ih =>
    obtain ⟨trace,related⟩ := ih (oracle i)
    exact ⟨congrArg (fun log => (i,oracle i)::log) trace,related⟩

/-- Independent-answer observation transport, without requiring distinct reads
or replacing repeated-address answers by a function. Observers see the full log. -/
theorem SameReads.independentMean_le {I Answer A B : Type} [Fintype Answer]
    {R : A → B → Prop} {p : Program I Answer A} {q : Program I Answer B}
    (h : SameReads R p q) (first : View I Answer A → ℚ) (second : View I Answer B → ℚ)
    (terminal : ∀ log a b,R a b → first (log,a)≤second (log,b)) :
    independentMean p first ≤ independentMean q second := by
  induction h generalizing first second with
  | done related => exact terminal [] _ _ related
  | ask i next ih =>
    apply FS.mean_mono
    intro reply
    apply ih reply
    intro log a b related
    exact terminal ((i,reply)::log) a b related

/-- The same transport for actual memoized-oracle answers, from ANY initial
cache, preserving hits, misses, replies and ordering. -/
theorem SameReads.lazyMean_le {I Answer A B : Type} [Fintype Answer] [DecidableEq I]
    {R : A → B → Prop} {p : Program I Answer A} {q : Program I Answer B}
    (h : SameReads R p q) (table : Table I Answer)
    (first : View I Answer A → ℚ) (second : View I Answer B → ℚ)
    (terminal : ∀ log a b,R a b → first (log,a)≤second (log,b)) :
    lazyMean p table first≤lazyMean q table second := by
  induction h generalizing table first second with
  | done related => exact terminal [] _ _ related
  | ask i next ih =>
    cases cached : table i with
    | some reply =>
      simp only [lazyMean,cached]
      apply ih reply
      intro log a b related
      exact terminal ((i,reply)::log) a b related
    | none =>
      simp only [lazyMean,cached]
      apply FS.mean_mono
      intro reply
      apply ih reply
      intro log a b related
      exact terminal ((i,reply)::log) a b related

#print axioms paired_related
#print axioms SameReads.eval_related
#print axioms SameReads.independentMean_le
#print axioms SameReads.lazyMean_le
end AspisS1QueryProgramRelation
