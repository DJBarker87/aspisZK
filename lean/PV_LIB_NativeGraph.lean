import PV_LIB_Observation
import PV_W1_ArgumentEffects
set_option autoImplicit false
noncomputable section
namespace PV_LIB_NativeGraph
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
/-- This is the exact let-bound output of ArgumentEffects.Post/full_reply.
The explicit effects family is an environment input, not a chosen identity. -/
def internalModel {E : Type} (C : Carrier OWNER Data) (d : Entry)
    (H : Backend E) (w : OWNER) (events : List E) (changes : Address → Option Data) :=
  deliver C (PV_W1_ArgumentEffects.afterEffects C d w changes)
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child d.callee d.store.nextActivation d.arguments) w) events

def model {E : Type} (C : Carrier OWNER Data) (d : Entry)
    (H : Backend E) (w : OWNER) (events : List E) (changes : Address → Option Data) :=
  PV_LIB.observe (internalModel C d H w events changes)

theorem certified {E : Type} (C : Carrier OWNER Data) (d : Entry)
    (H : Backend E) (w : OWNER) (events : List E) (changes : Address → Option Data)
    (pre : PV_W1_ClosedLeaves.Pre d w) :
    model C d H w events changes = PV_LIB.observe (internalModel C d H w events changes) ∧
      PV_W1_ArgumentEffects.Post C d H w events changes :=
  ⟨rfl,PV_W1_ArgumentEffects.full_reply C d H w events changes pre⟩
#print axioms certified
end PV_LIB_NativeGraph
