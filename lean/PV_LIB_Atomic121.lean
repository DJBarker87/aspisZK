import PV_LIB_LeafObservation
import PV_FN_THREAD_f121Value
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Atomic121
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
open PV_THR2_LibrarySemantics_AtomicUsizeNew
/-- Provider's function of the exact emitted request and explicit environment.
The existing documented fact constrains successful replies to hold n. It is
not used as a relational child law and does not select a successful branch. -/
def internalModel {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (changes : Address → Option Data) (n : Nat) :=
  let d := entry e n
  (PV_W1_ArgumentEffects.finalStore C d w changes,
   PV_THR2_OwnUniformResourceHandler.lift H
     (.child d.callee d.store.nextActivation d.arguments) w)
def model {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (changes : Address → Option Data) (n : Nat) :=
  PV_LIB.leafObserve (internalModel C e H w changes n)
def law {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (changes : Address → Option Data) (n : Nat)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) E) : Prop :=
  out = model C e H w changes n

theorem certified {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (events : List E) (changes : Address → Option Data) (n : Nat)
    (pre : PV_W1_ClosedLeaves.Pre e w) (semantics : Fact C e H w changes n) :
    law C e H w changes n (PV_LIB.leafObserve (internalModel C e H w changes n)) ∧
    PV_FN_THREAD_f121.PostValue C e H w events changes n :=
  ⟨rfl,PV_FN_THREAD_f121.contract_value C e H w events changes n pre semantics⟩

theorem returned_value {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (changes : Address → Option Data) (n : Nat)
    (semantics : Fact C e H w changes n) (result : Data)
    (answer : (internalModel C e H w changes n).2.answer = .returned (.ok result)) :
    Holds result n := (semantics result answer).value
#print axioms certified
#print axioms returned_value
end PV_LIB_Atomic121
