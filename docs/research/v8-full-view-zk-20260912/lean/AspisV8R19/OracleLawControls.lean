import AspisV8R19.MemoizedProgramLaw

/-! Small exact controls: querying twice is not two fresh samples, and a
publication filter can destroy uniformity while preserving the oracle law. -/
set_option autoImplicit false
namespace AspisV8R19.OracleLawControls
open MemoizedProgramLaw OracleResampling AspisV8PairedCommitment
variable {I A : Type}

def repeatQuery (i : I) : Program I A (A × A) :=
  .ask i (fun a => .ask i (fun b => .done (a,b)))

theorem repeat_eval (H : I → A) (i : I) :
    eval H (repeatQuery i) = ([(i,H i),(i,H i)],(H i,H i)) := rfl

theorem repeat_lazy [Fintype A] [DecidableEq I] (i : I)
    (observe : View I A (A × A) → ℚ) :
    lazyMean (repeatQuery i) (fun _ => none) observe =
      mean (fun a => observe ([(i,a),(i,a)],(a,a))) := by
  simp [repeatQuery,lazyMean,put]

theorem independent_repeat_rejected (H : Unit → Bool) :
    eval H (repeatQuery ()) ≠ ([((),false),((),true)],(false,true)) := by
  rw [repeat_eval]
  intro h
  have hp := congrArg (fun r : View Unit Bool (Bool × Bool) => r.2) h
  have h1 := congrArg Prod.fst hp
  have h2 := congrArg Prod.snd hp
  exact Bool.false_ne_true (h1.symm.trans h2)

def publishTrue : Program Unit Bool (Option Bool) :=
  .ask () (fun a => .done (if a then some a else none))

theorem published_value_true (H : Unit → Bool) (b : Bool)
    (published : (eval H publishTrue).2 = some b) : b = true := by
  cases h : H () <;> simp [publishTrue,eval,h] at published ⊢
  exact published

theorem rejected_outcome_retained (H : Unit → Bool) (h : H () = false) :
    eval H publishTrue = ([((),false)],none) := by simp [publishTrue,eval,h]

theorem publication_event_law (event : View Unit Bool (Option Bool) → Prop)
    [DecidablePred event] :
    mean (fun H => if event (eval H publishTrue) then 1 else 0) =
      lazyMean publishTrue (fun _ => none) (fun r => if event r then 1 else 0) :=
  outcome_event_law publishTrue event

#print axioms repeat_eval
#print axioms repeat_lazy
#print axioms independent_repeat_rejected
#print axioms published_value_true
#print axioms rejected_outcome_retained
#print axioms publication_event_law
end AspisV8R19.OracleLawControls
