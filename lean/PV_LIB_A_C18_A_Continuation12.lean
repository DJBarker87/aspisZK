import PV_LIB_A_PrefixMachine11
import PV_THR2_IntrinsicAtContinuation
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_Continuation12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- Source-frontier lifting of the existing trace certificate. Other outcomes
use zero steps; no late destructor or unrelated caller instruction is run. -/
theorem trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler)
    (nodes : List PV_STX2_SliceSyntax.Node) (cost : Config → OWNER → Nat)
    (certificate : ∀ (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config),
      PV_THR2_IntrinsicAtContinuation.Ready nodes c →
      Trace C K P H (cost c w) ⟨⟨.running c,w,es⟩,stack⟩)
    (q : State) :
    Trace C K P H (PV_THR2_IntrinsicAtContinuation.steps nodes cost q) q := by
  classical
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases status with
  | running c =>
    by_cases h : PV_THR2_IntrinsicAtContinuation.Ready nodes c
    · simpa only [PV_THR2_IntrinsicAtContinuation.steps,if_pos h] using certificate c w es stack h
    · simp only [PV_THR2_IntrinsicAtContinuation.steps,if_neg h]; trivial
  | returned r s => trivial
  | fault f s => trivial
  | undefined site s => trivial

/-- Reuse the provider's at-continuation run and ONE corrected trace lift. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (nodes : List PV_STX2_SliceSyntax.Node) (cost : Config → OWNER → Nat)
    (finish : Config → OWNER → List PV_RJ4IDB.NativeEvent → List Config → State)
    (quiet : ∀ (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config),
      PV_THR2_IntrinsicAtContinuation.Ready nodes c →
      Trace C K P H (cost c w) ⟨⟨.running c,w,es⟩,stack⟩)
    (original : ∀ (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config),
      PV_THR2_IntrinsicAtContinuation.Ready nodes c →
      PV_THR2_IntrinsicState.advance C K P H (cost c w) ⟨⟨.running c,w,es⟩,stack⟩ = finish c w es stack)
    (q : State) :
    advance C K P resources encode H values (PV_THR2_IntrinsicAtContinuation.steps nodes cost q) ⟨q,none⟩ =
      ⟨PV_THR2_IntrinsicAtContinuation.after nodes finish q,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K P resources encode H values _ _
    (trace C K P H nodes cost quiet q)]
  exact congrArg (fun q => (⟨q,none⟩ : SourceState))
    (PV_THR2_IntrinsicAtContinuation.run C K P H nodes cost finish original q)

#print axioms trace
#print axioms run
end PV_LIB_A_Continuation12
