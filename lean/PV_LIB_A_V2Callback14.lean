import PV_LIB_A_F219Enter316Any14
import PV_LIB_A_V2Composition14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2Callback14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_PrefixMachine11
abbrev finish := PV_LIB_A_F219Enter31614.finish
abbrev steps := PV_LIB_A_F219Enter31614.steps
abbrev after := PV_LIB_A_F219Enter31614.after
theorem issue (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values 1
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 16,loops := loops},
        parents,PV_LIB_A_CallbackTail14.stored s a⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (PV_LIB_A_F219Selected14.parent s a parents loops),w,es⟩,stack⟩ := by
  have h := PV_LIB_A_V2Frontiers14.issue C K P resources encode H values
    PV_LIB_A_F219Issue31813.src PV_LIB_A_F219Issue31813.rest (by decide) (by intro s a w; rfl)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 16,loops := loops},
      parents,PV_LIB_A_CallbackTail14.stored s a⟩,w,es⟩,stack⟩
  have ready : PV_THR2_IntrinsicAtContinuation.Ready
      (PV_LIB_A_StructuredFrontier13.node PV_LIB_A_F219Issue31813.src :: PV_LIB_A_F219Issue31813.rest)
      ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 16,loops := loops},
        parents,PV_LIB_A_CallbackTail14.stored s a⟩ := ⟨rfl,rfl,rfl,rfl⟩
  simp only [PV_LIB_A_F219Issue31813.steps,PV_LIB_A_F219Issue31813.after,
    PV_LIB_A_CallIssue13.steps,PV_LIB_A_CallIssue13.after,PV_THR2_IntrinsicAtContinuation.steps,
    PV_THR2_IntrinsicAtContinuation.after,if_pos ready,PV_LIB_A_CallIssue13.finish,
    PV_THR2_IntrinsicFrameCall.after,show PV_LIB_A_F219Issue31813.src.2.2.2.1 =
      [.move (.local 6),.move (.local 7),.move (.local 8)] from rfl,PV_LIB_A_F219Selected14.operands] at h
  exact h


/-- Transfer the actual source-selected invocation to ORIGINAL v2, retaining
all source fields and the whole suspended parent. -/
theorem invoke (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_StoreActionTable.step C K P resources encode H values
      ⟨⟨.running (PV_LIB_A_F219Selected14.parent s a parents loops),w,es⟩,stack⟩ =
      finish ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 11,loops := loops},parents,s⟩ w es stack := by
  have source := PV_LIB_A_F219Selected14.invoke C K P resources encode H values s a parents loops w es stack
  have neutral : SourceNeutral P ⟨⟨.running (PV_LIB_A_F219Selected14.parent s a parents loops),w,es⟩,stack⟩ :=
    (PV_LIB_A_IntrinsicInvoke13.quiet P
      (PV_THR2_Catch219Call318.moved (PV_LIB_A_CallbackTail14.stored s a) a) a parents loops
      (PV_THR2_Catch219Call318.args a) 5 w es stack).1
  rw [PV_LIB_A_V2Neutral14.successor_step C K P resources encode H values _ neutral] at source
  exact congrArg SourceState.base source

theorem exact_tail (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_StoreActionTable.advance (PV_THR2_EntryDynamic.carrier C b) K P resources encode H values 7
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 11,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      finish ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 11,loops := loops},parents,s⟩ w es stack := by
  have off : PV_LIB_A_SourceSequence13.sites PV_LIB_A_CallbackTail14.seq := by
    change (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ True
    decide
  have cert := PV_LIB_A_SourceSequence13.certified (PV_THR2_EntryDynamic.carrier C b) K P H
    PV_LIB_A_CallbackTail14.seq s a parents loops (PV_THR2_F219.live.body.drop 16) w es stack off
  have first := PV_LIB_A_V2TraceTransport14.run (PV_THR2_EntryDynamic.carrier C b) K P resources encode H values
    _ _ cert.1
  rw [cert.2] at first
  rw [PV_LIB_A_CallbackTail14.shape,PV_LIB_A_CallbackTail14.cost,PV_LIB_A_CallbackTail14.result] at first
  change PV_LIB_StoreActionTable.advance _ _ _ _ _ _ _ (5+(1+1)) _ = _
  rw [PV_LIB_A_V2Composition14.advance_add,first,PV_LIB_A_V2Composition14.advance_add,issue]
  simp only [PV_LIB_StoreActionTable.advance]
  exact invoke _ K P resources encode H values s a parents loops w es stack

theorem run (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance (PV_THR2_EntryDynamic.carrier C b) K P resources encode H values
      (steps q) q = after q := by
  classical
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases status with
  | running c =>
    by_cases ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F219.live.body.drop 11) c
    · simp only [steps,PV_LIB_A_F219Enter31614.steps,PV_THR2_IntrinsicAtContinuation.steps,
        after,PV_LIB_A_F219Enter31614.after,PV_THR2_IntrinsicAtContinuation.after,if_pos ready]
      rw [PV_THR2_IntrinsicAtContinuation.frame c ready]
      exact exact_tail C b K P resources encode H values c.store c.frame.activation c.callers c.frame.loops w es stack
    · simp only [steps,PV_LIB_A_F219Enter31614.steps,PV_THR2_IntrinsicAtContinuation.steps,
        after,PV_LIB_A_F219Enter31614.after,PV_THR2_IntrinsicAtContinuation.after,if_neg ready,PV_LIB_StoreActionTable.advance]
  | returned r s => rfl
  | fault f s => rfl
  | undefined site s => rfl

#print axioms issue
#print axioms invoke
#print axioms exact_tail
#print axioms run
end PV_LIB_A_V2Callback14
