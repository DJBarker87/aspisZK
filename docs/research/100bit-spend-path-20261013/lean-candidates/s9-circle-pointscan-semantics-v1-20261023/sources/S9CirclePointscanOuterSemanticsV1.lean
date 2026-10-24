import S9CirclePointscanBodySemanticsV1
import S9CirclePointscanControlV1
import S9StatementSourceLoopFactsV1
import S9LoopInvariantPropertyV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9CirclePointscanOuterSemanticsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9FactorTableSemanticsV1 AspisR1S9CirclePointscanModelV1

private def invariant (before : Table) (z : Array Point 2#usize)
    (s : R × Factors) : Prop :=
  s.1.end=2#usize ∧ s.1.start.val ≤ 2 ∧ Meaning s.2 (circleScanTable before z s.1.start.val)
private def measure (s : R × Factors) : Nat := s.1.end.val-s.1.start.val
private def step (z : Array Point 2#usize) (s : R × Factors) :
    Result (ControlFlow (R × Factors) Factors) :=
  AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body z s.1 s.2

/-- Both complete native circle-factor rows and the untouched statement rows
come from this same accepted actual outer scan. -/
theorem circle_outer_success_meaning
    (before : Table) (z : Array Point 2#usize) (factors out : Factors)
    (hz : AspisR1S9ConstructorV3PointScanBodyCanonicalV1.PointsCanonical z)
    (hm : Meaning factors before)
    (hloop : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1
      { start:=0#usize, «end»:=2#usize } z factors = .ok out) :
    Meaning out (circleScanTable before z 2) := by
  let post := fun result => Meaning result (circleScanTable before z 2)
  have hdone : ∀ s result, invariant before z s →
      step z s=.ok (.done result) → post result := by
    rintro ⟨iter,fs⟩ result hs hstep
    rcases hs with ⟨hend,hhi,hmeaning⟩
    change AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body z iter fs=
      .ok (.done result) at hstep
    obtain ⟨hout,iterNext,hnext⟩ :=
      AspisR1S9CirclePointscanControlV1.body_done_execution z iter fs result hstep
    have hstop := AspisR1S9StatementSourceLoopFactsV1.next_none_stop iter iterNext hnext
    rw [hend] at hstop
    change 2 ≤ iter.start.val at hstop
    change iter.start.val ≤ 2 at hhi
    have he : iter.start.val=2 := by omega
    change Meaning result (circleScanTable before z 2)
    rw [hout]
    simpa only [he] using hmeaning
  have hcont : ∀ s s', invariant before z s →
      step z s=.ok (.cont s') → invariant before z s' := by
    rintro ⟨iter,fs⟩ ⟨iterNext,fsNext⟩ hs hstep
    rcases hs with ⟨hend,hhi,hmeaning⟩
    change AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body z iter fs=
      .ok (.cont (iterNext,fsNext)) at hstep
    obtain ⟨hstart,hend',hm'⟩ :=
      AspisR1S9CirclePointscanBodySemanticsV1.pointscan_body_success_meaning
        before z iter iterNext fs fsNext hz hend hmeaning hstep
    obtain ⟨k,point,q,i,old,back,rowOut,x,hnext,hrest⟩ :=
      AspisR1S9ConstructorV3PointScanBodyCanonicalV1.pointscan_body_success_has_execution
        z iter iterNext fs fsNext hstep
    have hlt := (next_some_progress iter iterNext k hnext).1
    rw [hend] at hlt
    change iter.start.val<2 at hlt
    refine ⟨hend',?_,hm'⟩
    change iterNext.start.val ≤ 2
    omega
  have hdec : ∀ s s', step z s=.ok (.cont s') → measure s'<measure s := by
    rintro ⟨iter,fs⟩ ⟨iterNext,fsNext⟩ hstep
    change AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body z iter fs=
      .ok (.cont (iterNext,fsNext)) at hstep
    obtain ⟨k,point,q,i,old,back,rowOut,x,hnext,hrest⟩ :=
      AspisR1S9ConstructorV3PointScanBodyCanonicalV1.pointscan_body_success_has_execution
        z iter iterNext fs fsNext hstep
    obtain ⟨hlt,hk,hstart,hend⟩ := next_some_progress iter iterNext k hnext
    simp only [measure,hstart,hend]
    omega
  have hi : invariant before z ({start:=0#usize,«end»:=2#usize},factors) := by
    refine ⟨rfl,?_,?_⟩
    · change 0 ≤ 2
      omega
    · change Meaning factors (circleScanTable before z 0)
      simpa only [circleScan_empty] using hm
  have hl : Aeneas.Std.loop (step z)
      ({start:=0#usize,«end»:=2#usize},factors)=.ok out := by
    change Aeneas.Std.loop (step z)
      ({start:=0#usize,«end»:=2#usize},factors)=.ok out at hloop
    exact hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    (step z) measure (invariant before z) post hdone hcont hdec _ out hi hl

/-- The actual same input supplies its initial table meaning. No independent
factor meaning or successful child call is assumed. -/
theorem circle_outer_success_actual_table
    (z : Array Point 2#usize) (factors out : Factors)
    (hz : AspisR1S9ConstructorV3PointScanBodyCanonicalV1.PointsCanonical z)
    (hloop : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1
      { start:=0#usize, «end»:=2#usize } z factors=.ok out) :
    Meaning out (circleScanTable (rawTable factors) z 2) ∧
      ∀ k d i, k<3 → circleScanTable (rawTable factors) z 2 k d i=rawTable factors k d i := by
  exact ⟨circle_outer_success_meaning (rawTable factors) z factors out hz
    (rawTable_meaning factors) hloop,
    fun k d i hk => circleScan_statement_frame (rawTable factors) z 2 k d i hk⟩

#print axioms circle_outer_success_meaning
#print axioms circle_outer_success_actual_table
end AspisR1S9CirclePointscanOuterSemanticsV1
