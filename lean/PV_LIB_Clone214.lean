import PV_LIB_Observation
import PV_W1_ClosedLeaves
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Clone214
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame

def internalModel {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (reference : Data) (events : List E) :=
  let d := PV_W1_NamedLeafBoundary.entry e PV_THR2_OperatorSites.clone214 [reference]
  let adapted := PV_THR2_OperatorCloneHandler.handler C (pending d)
    (PV_THR2_OwnUniformResourceHandler.lift H)
  deliver C d (adapted (.child d.callee e.store.nextActivation [reference]) w) events

def model {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (reference : Data) (events : List E) :=
  PV_LIB.observe (internalModel C e H w reference events)
def law {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (reference : Data) (events : List E)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model C e H w reference events

theorem certified {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (reference : Data) (events : List E)
    (pre : PV_W1_ClosedLeaves.Pre e w) :
    law C e H w reference events (PV_LIB.observe (internalModel C e H w reference events)) ∧
      PV_W1_ClosedLeaves.Post214 C e H w reference events :=
  ⟨rfl,PV_W1_ClosedLeaves.f214 C e H w reference events pre⟩
#print axioms certified
end PV_LIB_Clone214
