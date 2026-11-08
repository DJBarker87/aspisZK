import PV_LIB_A_F219Selected14
import PV_LIB_A_FrontierRun14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F219Enter31614
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11

def finish (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) : State :=
  let p := PV_LIB_A_F219Selected14.parent c.store c.frame.activation c.callers c.frame.loops
  ⟨⟨.running (PV_THR2_CallbackSegment.enter p PV_THR2_F316.live
    [PV_STX2_TypedReferences.reference ⟨c.frame.activation,2,[]⟩ .null]).callback,w,es⟩,p :: stack⟩

def steps (q : State) := PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F219.live.body.drop 11) (fun _ _ => 7) q
def after := PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F219.live.body.drop 11) finish

/-- The actual source tail constructs both callbacks and the Data pointer,
issues9196, then enters316. This includes source stores and the complete suspended
parent. It consumes no native answer and assumes no selector or readback. -/
theorem exact_tail (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_A_PrefixMachine11.advance (PV_THR2_EntryDynamic.carrier C b) K (PV_THR2_CatchChildren.table P)
      resources encode H values 7
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 11,loops := loops},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨finish ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 11,loops := loops},parents,s⟩ w es stack,none⟩ := by
  have off : PV_LIB_A_SourceSequence13.sites PV_LIB_A_CallbackTail14.seq := by
    change (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ (219 : Nat) ≠ 361 ∧ True
    decide
  have first := PV_LIB_A_SourceSequence13.run (PV_THR2_EntryDynamic.carrier C b) K
    (PV_THR2_CatchChildren.table P) resources encode H values PV_LIB_A_CallbackTail14.seq s a parents loops
    (PV_THR2_F219.live.body.drop 16) w es stack off
  rw [PV_LIB_A_CallbackTail14.shape,PV_LIB_A_CallbackTail14.cost,PV_LIB_A_CallbackTail14.result] at first
  change PV_LIB_A_PrefixMachine11.advance _ _ _ _ _ _ _ (5+(1+1)) _ = _
  rw [advance_add,first,advance_add,PV_LIB_A_F219Selected14.issue]
  simp only [PV_LIB_A_PrefixMachine11.advance]
  exact PV_LIB_A_F219Selected14.invoke _ K _ resources encode H values s a parents loops w es stack

theorem run (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_A_PrefixMachine11.advance (PV_THR2_EntryDynamic.carrier C b) K (PV_THR2_CatchChildren.table P)
      resources encode H values (steps q) ⟨q,none⟩ = ⟨after q,none⟩ := by
  apply PV_LIB_A_FrontierRun14.run
  intro c w es stack ready
  rw [PV_THR2_IntrinsicAtContinuation.frame c ready]
  exact exact_tail C b K P resources encode H values c.store c.frame.activation c.callers c.frame.loops w es stack

#print axioms finish
#print axioms exact_tail
#print axioms run
end PV_LIB_A_F219Enter31614
