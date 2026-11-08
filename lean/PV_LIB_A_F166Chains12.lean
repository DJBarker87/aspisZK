import PV_LIB_A_Continuation12
import PV_LIB_A_ChainTrace11
import PV_THR2_Source166Prologue
import PV_THR2_Source166Captures
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F166Chains12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- Exact166 source chain, outside registration/allocation action sites. -/
theorem prologue_sites : PV_LIB_A_ChainTrace11.Sites PV_THR2_Source166Prologue.chain := by
  change (166 : Nat) ≠ 361 ∧ (166 : Nat) ≠ 361 ∧ (166 : Nat) ≠ 361 ∧ (166 : Nat) ≠ 361 ∧ (166 : Nat) ≠ 361 ∧ (166 : Nat) ≠ 361 ∧ True
  decide

theorem prologue_trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (q : State) :
    Trace C K P H (PV_THR2_Source166Prologue.steps C q) q := by
  apply PV_LIB_A_Continuation12.trace
  intro c w es stack h
  rw [PV_THR2_IntrinsicAtContinuation.frame c h]
  change Trace C K P H
    (PV_THR2_IntrinsicFrameChain.steps C c.frame.activation w PV_THR2_Source166Prologue.chain c.store)
    ⟨⟨.running ⟨{activation := c.frame.activation,remaining := PV_THR2_F166.live.body,loops := c.frame.loops},c.callers,c.store⟩,w,es⟩,stack⟩
  rw [← PV_THR2_Source166Prologue.shape]
  exact PV_LIB_A_ChainTrace11.trace C K P H _ _ _ _ _ _ w es stack prologue_sites

/-- Corrected166 chain, retaining every failed boolean/read/capture binding. -/
theorem prologue (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (PV_THR2_Source166Prologue.steps C q) ⟨q,none⟩ =
      ⟨PV_THR2_Source166Prologue.after C q,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K P resources encode H values _ _ (prologue_trace C K P H q)]
  exact congrArg (fun q => (⟨q,none⟩ : SourceState)) (PV_THR2_Source166Prologue.run C K P H q)

/-- Exact166 source chain, outside registration/allocation action sites. -/
theorem captures_sites : PV_LIB_A_ChainTrace11.Sites PV_THR2_Source166Captures.chain := by
  change (166 : Nat) ≠ 361 ∧ (166 : Nat) ≠ 361 ∧ (166 : Nat) ≠ 361 ∧ (166 : Nat) ≠ 361 ∧ (166 : Nat) ≠ 361 ∧ True
  decide

theorem captures_trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (q : State) :
    Trace C K P H (PV_THR2_Source166Captures.steps C q) q := by
  apply PV_LIB_A_Continuation12.trace
  intro c w es stack h
  rw [PV_THR2_IntrinsicAtContinuation.frame c h]
  change Trace C K P H
    (PV_THR2_IntrinsicFrameChain.steps C c.frame.activation w PV_THR2_Source166Captures.chain c.store)
    ⟨⟨.running ⟨{activation := c.frame.activation,remaining := PV_THR2_F166.live.body.drop 7,loops := c.frame.loops},c.callers,c.store⟩,w,es⟩,stack⟩
  rw [← PV_THR2_Source166Captures.shape]
  exact PV_LIB_A_ChainTrace11.trace C K P H _ _ _ _ _ _ w es stack captures_sites

/-- Corrected166 chain, retaining every failed boolean/read/capture binding. -/
theorem captures (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (PV_THR2_Source166Captures.steps C q) ⟨q,none⟩ =
      ⟨PV_THR2_Source166Captures.after C q,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K P resources encode H values _ _ (captures_trace C K P H q)]
  exact congrArg (fun q => (⟨q,none⟩ : SourceState)) (PV_THR2_Source166Captures.run C K P H q)

#print axioms prologue_sites
#print axioms prologue_trace
#print axioms prologue
#print axioms captures_sites
#print axioms captures_trace
#print axioms captures
end PV_LIB_A_F166Chains12
