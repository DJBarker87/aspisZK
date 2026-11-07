import PV_FN_SLICE_f7_Statements
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f7_Joins
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_SLICE_f7

theorem issueDrop : IssueDrop := by
  intro E x capture cell
  change PV_THR2_IntrinsicState.advance _ _ _ _ 1
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.node4 :: PV_STX2_SliceF7.program.body.drop 5},
      x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = _
  unfold PV_STX2_SliceF7.node4
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
    PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,native,adopt,PV_STX2_Native.step,
    PV_STX2_Store.read,locate,readAddress,cell,
    PV_FN_SLICE_f7_AfterDrop.config,PV_FN_SLICE_f7_AfterDrop.waiting,
    PV_FN_SLICE_f7_AfterDrop.source,PV_STX2_SliceF7.node4]

theorem receiveDrop : ReceiveDrop := by
  intro E x capture
  generalize reply : x.H (.drop PV_FN_SLICE_f7_AfterDrop.source.1 capture) x.w = r
  rcases r with ⟨answer,w,events⟩
  cases answer with
  | returned result =>
    cases result <;>
      simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
        PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
        PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
        PV_STX2_SliceMachine.step,PV_FN_SLICE_f7_AfterDrop.received,
        PV_FN_SLICE_f7_AfterDrop.config,PV_FN_SLICE_f7_AfterDrop.waiting,
        PV_THR2_ChildBoundary.delivered,PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Pinned.eraseFault,PV_STX2_PinnedConfig,
        PV_STX2_Native.reply,PV_STX2_Native.storeResult,native,adopt,locate,writeAddress,reply]
  | fault reason =>
    cases reason <;>
      simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
        PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
        PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
        PV_STX2_SliceMachine.step,PV_FN_SLICE_f7_AfterDrop.received,
        PV_FN_SLICE_f7_AfterDrop.config,PV_FN_SLICE_f7_AfterDrop.waiting,
        PV_THR2_ChildBoundary.delivered,PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Pinned.eraseFault,PV_STX2_PinnedConfig,
        PV_STX2_Native.reply,native,adopt,reply]
  | pending =>
    simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
      PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
      PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
      PV_STX2_SliceMachine.step,PV_FN_SLICE_f7_AfterDrop.received,
      PV_FN_SLICE_f7_AfterDrop.config,PV_FN_SLICE_f7_AfterDrop.waiting,
      PV_THR2_ChildBoundary.delivered,PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Pinned.eraseFault,PV_STX2_PinnedConfig,
      PV_STX2_Native.reply,native,adopt,reply]

theorem successBoundary : SuccessBoundary := by
  intro E x v d
  rfl

theorem successValue : SuccessValue := by
  intro E x v d
  simp only [successStore,PV_FN_SLICE_f8_Suffix.finalStore,
    PV_FN_SLICE_f8_FullReplies.suffix,PV_FN_SLICE_f7_Prefix.input8,
    PV_FN_SLICE_f7_Prefix.parent8,write,ite_true]

theorem otherJoin : OtherJoin := by
  intro E x pre o other
  cases o with
  | success v d => exact False.elim (other v d rfl)
  | failure e d =>
    refine ⟨1,?_⟩
    change PV_THR2_IntrinsicState.advance _ _ _ _ 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 4,waiting := some (PV_FN_SLICE_f7_Prefix.waiting x),completed := some (.fail e)},
        x.parent :: x.parents,d.store⟩,d.world,d.events⟩,x.stack⟩ = _
    exact PV_FN_W2_BinaryReturnOutcome.completed (PV_FN_SLICE_ValueCarrier.carrier x.C)
      x.K x.P x.H d.store x.a x.dest (PV_STX2_SliceF7.program.body.drop 4) []
      x.parent x.parents x.wait (PV_FN_SLICE_f7_Prefix.waiting x) (.fail e)
      PV_FN_SLICE_f7_Prefix.source.2.1 (PV_FN_SLICE_f7_Prefix.self x)
      (PV_FN_SLICE_f7_Prefix.tuple x) x.s.nextActivation d.world d.events x.stack
      pre.saved pre.action rfl
  | divergence d =>
    refine ⟨1,?_⟩
    change PV_THR2_IntrinsicState.advance _ _ _ _ 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 4,waiting := some (PV_FN_SLICE_f7_Prefix.waiting x),completed := some .div},
        x.parent :: x.parents,d.store⟩,d.world,d.events⟩,x.stack⟩ = _
    exact PV_FN_W2_BinaryReturnOutcome.completed (PV_FN_SLICE_ValueCarrier.carrier x.C)
      x.K x.P x.H d.store x.a x.dest (PV_STX2_SliceF7.program.body.drop 4) []
      x.parent x.parents x.wait (PV_FN_SLICE_f7_Prefix.waiting x) .div
      PV_FN_SLICE_f7_Prefix.source.2.1 (PV_FN_SLICE_f7_Prefix.self x)
      (PV_FN_SLICE_f7_Prefix.tuple x) x.s.nextActivation d.world d.events x.stack
      pre.saved pre.action rfl
  | fault reason d => exact ⟨0,rfl⟩
  | undefined site d => exact ⟨0,rfl⟩
  | pending q => exact ⟨0,rfl⟩

theorem dropJoin : DropJoin := by
  intro E x capture r saved action live
  rw [PV_FN_SLICE_f7_AfterDrop.received_eq]
  cases r with
  | mk answer w events =>
    cases answer with
    | pending => rfl
    | fault f => rfl
    | returned result =>
      cases result with
      | ok ignored =>
        rw [← PV_FN_SLICE_f7_AfterDrop.received_eq]
        exact PV_FN_SLICE_f7_AfterDrop.run x capture _
          ⟨live.1,saved,action,live.2⟩
      | fail e =>
        exact PV_FN_W2_DropReturnOutcome.completed (PV_FN_SLICE_ValueCarrier.carrier x.C)
          x.K x.P x.H x.s x.a x.dest (PV_STX2_SliceF7.program.body.drop 5) []
          x.parent x.parents x.wait (PV_FN_SLICE_f7_AfterDrop.waiting capture) (.fail e)
          PV_FN_SLICE_f7_AfterDrop.source.1 capture w (x.es ++ events) x.stack saved action rfl
      | div =>
        exact PV_FN_W2_DropReturnOutcome.completed (PV_FN_SLICE_ValueCarrier.carrier x.C)
          x.K x.P x.H x.s x.a x.dest (PV_STX2_SliceF7.program.body.drop 5) []
          x.parent x.parents x.wait (PV_FN_SLICE_f7_AfterDrop.waiting capture) .div
          PV_FN_SLICE_f7_AfterDrop.source.1 capture w (x.es ++ events) x.stack saved action rfl

/-- Use the provider Post directly. f7 neither executes f6 nor reconstructs
its full reply. The actual source173 resolver remains in f7's own Pre. -/
theorem through8 {E : Type} (x : Input E) (pre : Pre x) (callee8 : Callee8 x) :
    ∃ o : Outcome E,
      PV_FN_SLICE_f8_FullReplies.Executed6 (PV_FN_SLICE_f7_Prefix.input8 x) o ∧
      ∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
        (entry x) = after8 x o := by
  have closed8 := callee8 (PV_FN_SLICE_f7_Prefix.pre8 x pre.toPre pre.source6)
  obtain ⟨o,executed,pending,first,⟨n,body⟩,rest⟩ := closed8
  refine ⟨o,executed,4+1+n,?_⟩
  unfold entry
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_SLICE_f7_Prefix.run x pre.toPre,PV_FN_SLICE_f7_Into8.enter8 x pre.source8]
  exact body

theorem callee8_of_callee6 : Callee8From6 := by
  intro E x callee6 pre
  exact PV_FN_SLICE_f8.contract (PV_FN_SLICE_f7_Prefix.input8 x) pre callee6

theorem otherComposition {E : Type} (x : Input E) (pre : Pre x) (callee8 : Callee8 x) :
    ∃ o : Outcome E,
      PV_FN_SLICE_f8_FullReplies.Executed6 (PV_FN_SLICE_f7_Prefix.input8 x) o ∧
      (∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
        (entry x) = after8 x o) ∧
      ((∀ v d, o ≠ .success v d) →
        ∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
          (entry x) = otherFinish x o) := by
  obtain ⟨o,executed,n,reached⟩ := through8 x pre callee8
  refine ⟨o,executed,⟨n,reached⟩,?_⟩
  intro other
  obtain ⟨m,joined⟩ := otherJoin x pre o other
  refine ⟨n+m,?_⟩
  rw [PV_THR2_IntrinsicComposition.advance_add,reached]
  exact joined

theorem dropComposition : DropComposition := by
  intro E x capture cell saved action
  dsimp only
  intro live
  rw [PV_THR2_IntrinsicComposition.advance_add,
    PV_THR2_IntrinsicComposition.advance_add,issueDrop x capture cell,receiveDrop x capture]
  exact dropJoin x capture _ saved action live

#print axioms issueDrop
#print axioms receiveDrop
#print axioms successBoundary
#print axioms successValue
#print axioms otherJoin
#print axioms dropJoin
#print axioms dropComposition
#print axioms through8
#print axioms callee8_of_callee6
#print axioms otherComposition
set_option pp.fullNames true in
set_option pp.piBinderNames true in
set_option pp.proofs false in
#print otherComposition
end PV_FN_SLICE_f7_Joins
