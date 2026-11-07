import PV_LIB_LeafObservation
import PV_W1_DropLeaf
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Drop
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
/-- The deterministic function exported by CLOSED Drop, including the explicit
argument-reachable effects supplied by the environment. -/
def model {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (value : Data) (changes : Address → Option Data) :=
  PV_LIB.leafObserve (PV_W1_DropLeaf.call C e H w value changes)
def law {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (value : Data) (changes : Address → Option Data)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) E) : Prop :=
  out = model C e H w value changes

theorem certified {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (value : Data) (changes : Address → Option Data)
    (pre : PV_W1_DropLeaf.Pre e w) :
    law C e H w value changes (PV_LIB.leafObserve (PV_W1_DropLeaf.call C e H w value changes)) ∧
    PV_W1_DropLeaf.Post C e H w value changes :=
  ⟨rfl,PV_W1_DropLeaf.contract C e H w value changes pre⟩
#print axioms certified
end PV_LIB_Drop
