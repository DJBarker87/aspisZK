import PV_W5_F31Specification
import PV_STX2_ToVecConstructorEntry
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31Replies
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine PV_STX2_Source7ConstructorEntry

def received (D : Carrier OWNER Data) (s : Store Data) (parents : List Frame) (a : Nat)
    (length alloc layout : Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (prior : List PV_RJ4IDB.NativeEvent) : Prefix OWNER PV_RJ4IDB.NativeEvent :=
  let c := called s parents a length alloc layout
  let waiting : PV_STX2_Native.Waiting Data :=
    ⟨.child callee s.nextActivation [length,initValue,alloc,layout],.child s.nextActivation (.local 4),unwind⟩
  PV_STX2_SlicePrefixEvents.prepend prior
    (adopt c c.frame.remaining (PV_STX2_Pinned.reply D (native c []) waiting r))

theorem native_reply1 (D : Carrier OWNER Data) (K : Control) (H : PV_W5_F35Modes.HType)
    (s : Store Data) (parents : List Frame) (a : Nat) (length alloc layout : Data)
    (w : OWNER) :
    advance D K (fun _ => none) H 1 ⟨.running (called s parents a length alloc layout),w,[]⟩ =
      received D s parents a length alloc layout
        (H (.child callee s.nextActivation [length,initValue,alloc,layout]) w) [] := by
  rfl

theorem reply1 (resources : Resources) (encode : Encode) (D : Carrier OWNER Data) (K : Control)
    (H : PV_W5_F35Modes.HType) (s : Store Data) (parents : List Frame) (a : Nat)
    (length alloc layout : Data) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) :
    PV_STX2_Source7IterationBindings.advance resources encode D K (fun _ => none) H 1
      ⟨.running (called s parents a length alloc layout),w,prior⟩ =
    received D s parents a length alloc layout
      (H (.child callee s.nextActivation [length,initValue,alloc,layout]) w) prior := by
  let c := called s parents a length alloc layout
  have same : PV_STX2_Source7IterationBindings.step resources encode D K (fun _ => none) H c w =
      step D K (fun _ => none) H c w := by
    unfold PV_STX2_Source7IterationBindings.step
    rw [PV_STX2_IterationHandlerLocal.bindings2_step D K (fun _ => none) _ H c w (by
      intro q hq
      change some _ = some q at hq
      cases hq
      cases length <;> rfl)]
    exact PV_STX2_Source7QUniformAgreement2.neutral D K (fun _ => none) H c w ⟨True.intro,rfl⟩
  have old := native_reply1 D K H s parents a length alloc layout w
  have framed := congrArg (PV_STX2_SlicePrefixEvents.prepend prior) old
  rw [← PV_STX2_SlicePrefixEvents.advance_prepend] at framed
  change PV_STX2_Source7IterationBindings.advance resources encode D K (fun _ => none) H 1 ⟨.running c,w,prior⟩ = _
  simpa only [PV_STX2_Source7IterationBindings.advance,PV_STX2_SliceMachine.advance,same,
    PV_STX2_SlicePrefixEvents.prepend,List.append_nil,List.nil_append,received] using framed

/-- Whole own-entry prefix and arbitrary full f35 reply. The existing named
seven-step prefix is consumed once; no f35 instruction is traversed. -/
theorem source8 (resources : Resources) (encode : Encode) (D : Carrier OWNER Data) (K : Control)
    (H : PV_W5_F35Modes.HType) (s : Store Data) (parents : List Frame) (a : Nat)
    (length alloc layout : Data) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent)
    (input1 : s.cells ⟨a,1,[]⟩=some length)
    (input2 : s.cells ⟨a,2,[]⟩=some alloc)
    (input3 : s.cells ⟨a,3,[]⟩=some layout) :
    PV_STX2_Source7IterationBindings.advance resources encode (carrier D) K (fun _ => none) H 8
      ⟨.running ⟨{activation:=a,remaining:=PV_STX2_Source7CtorF31.program.body},parents,s⟩,w,prior⟩ =
    received (carrier D) s parents a length alloc layout
      (H (.child callee s.nextActivation [length,initValue,alloc,layout]) w) prior := by
  rw [show 8=7+1 by omega,PV_STX2_Source7IterationBindings.advance_add,
    PV_STX2_ToVecConstructorEntry.source7 resources encode D K (fun _ => none) H s parents w a
      length alloc layout prior input1 input2 input3]
  exact reply1 resources encode (carrier D) K H s parents a length alloc layout w prior

#print axioms native_reply1
#print axioms reply1
#print source8
#print axioms source8
end PV_W5_F31Replies
