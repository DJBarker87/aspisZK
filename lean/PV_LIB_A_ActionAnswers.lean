import PV_LIB_A_StoreActionMachine
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActionAnswers
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable

/-- Rust Result::Err with its actual generic/type metadata and payload. The
same constructor covers weak spurious failure even when expected equals old. -/
def casError (ty metadata payload : Data) : Data :=
  .object [("thread-aggregate-kind",.object [("Adt",.array [ty,.number 1,metadata])]),
    ("thread-aggregate-slots",.array [payload])]

/-- No inequality between expected and the loaded value is required. Failure
is an observed atomic answer, not a branch guessed from the source cell. -/
theorem weak_failure (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (fn reference expected replacement success failure ty metadata payload : Data)
    (s : Store Data) (w post : OWNER) (events : List PV_RJ4IDB.NativeEvent) :
    interpret C values (.primitive .cas530) fn [reference,expected,replacement,success,failure]
      s w ⟨.returned (.ok (casError ty metadata payload)),post,events⟩ = some s := rfl

theorem strong_failure (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (fn reference expected replacement success failure ty metadata payload : Data)
    (s : Store Data) (w post : OWNER) (events : List PV_RJ4IDB.NativeEvent) :
    interpret C values (.primitive .cas555) fn [reference,expected,replacement,success,failure]
      s w ⟨.returned (.ok (casError ty metadata payload)),post,events⟩ = some s := rfl

/-- Exact whole-delivery equality on a spurious weak failure, on arbitrary
source cells, worlds and event suffixes. This proves more than world framing.
There is no valid-write/success or non-spurious-failure premise. -/
theorem weak_failure_delivery (C : Carrier OWNER Data)
    (values : Values OWNER PV_RJ4IDB.NativeEvent) (c : Config) (w post : OWNER)
    (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (fn reference expected replacement success failure ty metadata payload : Data)
    (wait : PV_STX2_Native.Waiting Data) :
    deliver C values c w es stack
      ⟨.primitive .cas530,fn,wait,[reference,expected,replacement,success,failure]⟩
      ⟨.returned (.ok (casError ty metadata payload)),post,events⟩ =
      let q := PV_THR2_ChildBoundary.delivered C c wait
        ⟨.returned (.ok (casError ty metadata payload)),post,events⟩
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := rfl

/-- Both CAS variants preserve the exact pending administration on every
argument shape, including without dereferencing a cell that was not written. -/
theorem cas_pending (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w post : OWNER) (es events : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (fn : Data) (args : List Data)
    (wait : PV_STX2_Native.Waiting Data) :
    deliver C values c w es stack ⟨.primitive .cas530,fn,wait,args⟩ ⟨.pending,post,events⟩ =
      ⟨⟨.running c,post,es ++ events⟩,stack⟩ ∧
    deliver C values c w es stack ⟨.primitive .cas555,fn,wait,args⟩ ⟨.pending,post,events⟩ =
      ⟨⟨.running c,post,es ++ events⟩,stack⟩ := ⟨rfl,rfl⟩

/-- Faults retain the existing client-profile interpretation, including the
panic-to-abort mapping. No arbitrary CAS error can be replaced by Ok. -/
theorem cas_fault (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w post : OWNER) (es events : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (fn : Data) (args : List Data)
    (wait : PV_STX2_Native.Waiting Data) (fault : Fault) :
    (deliver C values c w es stack ⟨.primitive .cas530,fn,wait,args⟩ ⟨.fault fault,post,events⟩ =
      let q := PV_THR2_ChildBoundary.delivered C c wait ⟨.fault fault,post,events⟩
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩) ∧
    (deliver C values c w es stack ⟨.primitive .cas555,fn,wait,args⟩ ⟨.fault fault,post,events⟩ =
      let q := PV_THR2_ChildBoundary.delivered C c wait ⟨.fault fault,post,events⟩
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩) := ⟨rfl,rfl⟩

#print axioms weak_failure
#print axioms strong_failure
#print axioms weak_failure_delivery
#print axioms cas_pending
#print axioms cas_fault
end PV_LIB_A_ActionAnswers
