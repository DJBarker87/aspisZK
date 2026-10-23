import S9ConstructorV3CircleStepSemanticsV1
import S9ConstructorV3CircleControlV1
import S9StatementSourceLoopFactsV1
import S9LoopInvariantPropertyV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ConstructorV3CircleLoopSemanticsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3QMMulSemanticsV1
open AspisR1S9FactorTableSemanticsV1 AspisR1S9CircleFactorModelV1

private def invariant (before : Table) (original : ExactQM) (k : Usize)
    (s : R × Factors × Q) : Prop :=
  s.1.end=5#usize ∧ 1≤s.1.start.val ∧ s.1.start.val≤5 ∧ Can s.2.2 ∧
    decode s.2.2=base original s.1.start.val ∧
    Meaning s.2.1 (prefixTable before (3+k.val) 1 s.1.start.val original)

private def measure (s : R × Factors × Q) : Nat := s.1.end.val-s.1.start.val
private def step (k : Usize) (s : R × Factors × Q) :
    Result (ControlFlow (R × Factors × Q) Factors) :=
  AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body k s.1 s.2.1 s.2.2

/-- The accepted actual four-row circle-factor loop has its retained natural
circle-factor meanings and exact frame for all other entries. This generic
form admits any already-described initial table; the source-only entry below
supplies that description from the actual initial factors itself. -/
theorem circle_inner_success_meaning
    (before : Table) (original : ExactQM) (k : Usize) (factors out : Factors) (x : Q)
    (hk : k.val<2) (hx : Can x) (hxm : decode x=base original 1)
    (hm : Meaning factors before)
    (hloop : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0
      { start:=1#usize, «end»:=5#usize } factors k x = .ok out) :
    Meaning out (prefixTable before (3+k.val) 1 5 original) := by
  let post := fun (result : Factors) => Meaning result (prefixTable before (3+k.val) 1 5 original)
  have hdone : ∀ s result, invariant before original k s →
      step k s = .ok (.done result) → post result := by
    rintro ⟨iter,fs,q⟩ result hs hstep
    rcases hs with ⟨hend,hlo,hhi,hcan,hvalue,hmeaning⟩
    change AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
      k iter fs q = .ok (.done result) at hstep
    have hout := AspisR1S9ConstructorV3CircleControlV1.body_done_same_factors
      k iter fs q result hstep
    obtain ⟨iterNext,hnext⟩ := AspisR1S9ConstructorV3CircleControlV1.body_done_has_next_none
      k iter fs q result hstep
    have hstop := AspisR1S9StatementSourceLoopFactsV1.next_none_stop iter iterNext hnext
    rw [hend] at hstop
    change 5 ≤ iter.start.val at hstop
    change iter.start.val ≤ 5 at hhi
    have hfinished : iter.start.val=5 := by omega
    change Meaning result (prefixTable before (3+k.val) 1 5 original)
    rw [hout]
    simpa only [hfinished] using hmeaning
  have hcont : ∀ s s', invariant before original k s →
      step k s = .ok (.cont s') → invariant before original k s' := by
    rintro ⟨iter,fs,q⟩ ⟨iterNext,fsNext,qNext⟩ hs hstep
    rcases hs with ⟨hend,hlo,hhi,hcan,hvalue,hmeaning⟩
    change AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
      k iter fs q = .ok (.cont (iterNext,fsNext,qNext)) at hstep
    obtain ⟨hstart,hend',hcan',hvalue',hmeaning'⟩ :=
      AspisR1S9ConstructorV3CircleStepSemanticsV1.circle_body_success_model_step
        before original k iter iterNext fs fsNext q qNext hk hend hlo hcan hvalue hmeaning hstep
    obtain ⟨d,hnext⟩ := AspisR1S9ConstructorV3CircleControlV1.body_cont_has_next
      k iter fs q iterNext fsNext qNext hstep
    have hlt := (next_some_progress iter iterNext d hnext).1
    rw [hend] at hlt
    change iter.start.val<5 at hlt
    change 1 ≤ iter.start.val at hlo
    change iter.start.val ≤ 5 at hhi
    refine ⟨hend',?_,?_,hcan',hvalue',hmeaning'⟩
    · change 1 ≤ iterNext.start.val
      omega
    · change iterNext.start.val ≤ 5
      omega
  have hdec : ∀ s s', step k s = .ok (.cont s') → measure s' < measure s := by
    rintro ⟨iter,fs,q⟩ ⟨iterNext,fsNext,qNext⟩ hstep
    change AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
      k iter fs q = .ok (.cont (iterNext,fsNext,qNext)) at hstep
    obtain ⟨d,hnext⟩ := AspisR1S9ConstructorV3CircleControlV1.body_cont_has_next
      k iter fs q iterNext fsNext qNext hstep
    obtain ⟨hlt,hd,hstart,hend⟩ := next_some_progress iter iterNext d hnext
    simp only [measure,hstart,hend]
    omega
  have hi : invariant before original k
      ({start:=1#usize,«end»:=5#usize},factors,x) := by
    refine ⟨rfl,?_,?_,hx,hxm,?_⟩
    · change 1 ≤ 1
      omega
    · change 1 ≤ 5
      omega
    · change Meaning factors (prefixTable before (3+k.val) 1 1 original)
      simpa only [prefix_empty] using hm
  have hl : Aeneas.Std.loop (step k)
      ({start:=1#usize,«end»:=5#usize},factors,x) = .ok out := by
    change Aeneas.Std.loop (step k)
      ({start:=1#usize,«end»:=5#usize},factors,x) = .ok out at hloop
    exact hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    (step k) measure (invariant before original k) post hdone hcont hdec _ out hi hl

/-- The initial table description is derived from the actual same input;
no independent factor meaning is assumed. -/
theorem circle_inner_success_actual_table
    (original : ExactQM) (k : Usize) (factors out : Factors) (x : Q)
    (hk : k.val<2) (hx : Can x) (hxm : decode x=base original 1)
    (hloop : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0
      { start:=1#usize, «end»:=5#usize } factors k x = .ok out) :
    Meaning out (prefixTable (rawTable factors) (3+k.val) 1 5 original) :=
  circle_inner_success_meaning (rawTable factors) original k factors out x hk hx hxm
    (rawTable_meaning factors) hloop

#print axioms circle_inner_success_meaning
#print axioms circle_inner_success_actual_table
end AspisR1S9ConstructorV3CircleLoopSemanticsV1
