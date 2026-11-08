import PV_LIB_A_F219Enter31614
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F219Enter316Any14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11
abbrev finish := PV_LIB_A_F219Enter31614.finish
abbrev steps := PV_LIB_A_F219Enter31614.steps
abbrev after := PV_LIB_A_F219Enter31614.after
theorem issue (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_A_PrefixMachine11.advance C K P resources encode H values 1
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 16,loops := loops},
        parents,PV_LIB_A_CallbackTail14.stored s a⟩,w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running (PV_LIB_A_F219Selected14.parent s a parents loops),w,es⟩,stack⟩,none⟩ := by
  have h := PV_LIB_A_CallIssue13.run C K P resources encode H values
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

/-- The actual source tail constructs both callbacks and the Data pointer,
issues9196, then enters316. This includes source stores and the complete suspended
parent. It consumes no native answer and assumes no selector or readback. -/
theorem exact_tail (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_A_PrefixMachine11.advance (PV_THR2_EntryDynamic.carrier C b) K P
      resources encode H values 7
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 11,loops := loops},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨finish ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 11,loops := loops},parents,s⟩ w es stack,none⟩ := by
  have off : PV_LIB_A_SourceSequence13.sites PV_LIB_A_CallbackTail14.seq := by
    change (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ True
    decide
  have first := PV_LIB_A_SourceSequence13.run (PV_THR2_EntryDynamic.carrier C b) K
    P resources encode H values PV_LIB_A_CallbackTail14.seq s a parents loops
    (PV_THR2_F219.live.body.drop 16) w es stack off
  rw [PV_LIB_A_CallbackTail14.shape,PV_LIB_A_CallbackTail14.cost,PV_LIB_A_CallbackTail14.result] at first
  change PV_LIB_A_PrefixMachine11.advance _ _ _ _ _ _ _ (5+(1+1)) _ = _
  rw [advance_add,first,advance_add,issue]
  simp only [PV_LIB_A_PrefixMachine11.advance]
  exact PV_LIB_A_F219Selected14.invoke _ K _ resources encode H values s a parents loops w es stack

theorem run (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_A_PrefixMachine11.advance (PV_THR2_EntryDynamic.carrier C b) K P
      resources encode H values (steps q) ⟨q,none⟩ = ⟨after q,none⟩ := by
  apply PV_LIB_A_FrontierRun14.run
  intro c w es stack ready
  rw [PV_THR2_IntrinsicAtContinuation.frame c ready]
  exact exact_tail C b K P resources encode H values c.store c.frame.activation c.callers c.frame.loops w es stack

#print axioms issue
#print axioms exact_tail
#print axioms run
end PV_LIB_A_F219Enter316Any14
