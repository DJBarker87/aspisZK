import V7ProductionCallbacksR30ArrayCanonical

/-! Predicate preservation through the source array::from_fn recursion. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30FromFnCanonical
open V7ProductionCallbacksR30MutableCanonical

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do let value ← input; next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

theorem from_fn_list_all {T C : Type}
    (inst : core.ops.function.FnMut C Std.Usize T)
    (P : T → Prop) (I : C → Prop)
    (callCanonical : ∀ c index value next, I c →
      inst.call_mut c index = ok (value, next) → P value ∧ I next)
    (fuel : Nat) (index : Std.Usize) (state : C)
    (values : List T) (finalState : C) (initial : I state)
    (run : core.array.fromFnList inst fuel index state = ok (values, finalState)) :
    ∀ value ∈ values, P value := by
  induction fuel generalizing index state values finalState with
  | zero =>
      rw [core.array.fromFnList.eq_1] at run
      have valuesEmpty := congrArg Prod.fst (Result.ok.inj run)
      simp only at valuesEmpty
      rw [← valuesEmpty]
      simp
  | succ fuel ih =>
      cases fuel with
      | zero =>
          rw [core.array.fromFnList.eq_2] at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨⟨value, nextState⟩, callRun, run⟩ := run
          have valuesExact := congrArg Prod.fst (Result.ok.inj run)
          simp only at valuesExact
          rw [← valuesExact]
          intro target member
          simp only [List.mem_singleton] at member
          rw [member]
          exact (callCanonical state index value nextState initial callRun).1
      | succ remaining =>
          rw [core.array.fromFnList.eq_2] at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨⟨value, nextState⟩, callRun, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨nextIndex, nextIndexRun, run⟩ := run
          rw [bind_eq_ok_iff] at run
          obtain ⟨⟨tail, tailState⟩, tailRun, run⟩ := run
          have facts := callCanonical state index value nextState initial callRun
          have tailCanonical := ih nextIndex nextState tail tailState facts.2 tailRun
          have valuesExact := congrArg Prod.fst (Result.ok.inj run)
          simp only at valuesExact
          rw [← valuesExact]
          intro target member
          rcases List.mem_cons.mp member with same | inTail
          · exact same ▸ facts.1
          · exact tailCanonical target inTail

theorem from_fn_all {T C : Type} [Inhabited T]
    (inst : core.ops.function.FnMut C Std.Usize T)
    (P : T → Prop) (I : C → Prop)
    (callCanonical : ∀ c index value next, I c →
      inst.call_mut c index = ok (value, next) → P value ∧ I next)
    (N : Std.Usize) (state : C) (output : Array T N)
    (initial : I state) (run : core.array.from_fn N inst state = ok output) :
    SliceAll P output.to_slice := by
  unfold core.array.from_fn at run
  generalize listRun : core.array.fromFnList inst N.val 0#usize state = computation at run
  cases computation with
  | fail error => simp at run
  | div => simp at run
  | ok pair =>
      rcases pair with ⟨values, finalState⟩
      dsimp at run
      split at run
      · have outputExact : output.val = values :=
          congrArg Subtype.val (Result.ok.inj run).symm
        have allValues := from_fn_list_all inst P I callCanonical N.val 0#usize state
          values finalState initial listRun
        intro index bound
        change P output.val[index]!
        have indexBound : index < values.length := by
          change index < output.val.length at bound
          simpa [outputExact] using bound
        rw [outputExact, ← List.Inhabited_getElem_eq_getElem! values index indexBound]
        exact allValues _ (List.getElem_mem indexBound)
      · cases run

#print axioms from_fn_all
end V7ProductionCallbacksR30FromFnCanonical
