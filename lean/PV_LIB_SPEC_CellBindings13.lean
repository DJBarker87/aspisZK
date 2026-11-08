import PV_LIB_SPEC_TlsBindings13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_CellBindings13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

/-- Cell::replace returns the old source value. Its actual source write is
performed independently by the retained v2 table, with no equality of whole
stores/activation counters requested at a boundary. Cell::new is transparent.
The source bool specialization of Cell::set has no destructor. -/
def value (p : Parameters) (c : Config) (w : OWNER) (fn : Data) (args : List Data) : Option Data :=
  match PV_THR2_OffPath.functionId fn,args with
  | some 289,[reference,_] => do
    let address ← (runtime p).carrier.dereference w reference
    readAddress (runtime p).carrier c.store address
  | some 371,[input] => some input
  | _,_ => none

def reply (p : Parameters) (c : Config) (w : OWNER) (fn : Data) (args : List Data)
    (r : Reply OWNER Event Data) : Option (Reply OWNER Event Data) :=
  match r.answer with
  | .returned (.ok _) => do
    let v ← value p c w fn args
    pure ⟨.returned (.ok v),w,r.events⟩
  | _ => some {r with world := w}

/-- A replacement's RETURN value is derived from the reached source cell;
no old-value or post-write projection is passed in from a callee hypothesis. -/
theorem old_value (p : Parameters) (c : Config) (w : OWNER)
    (fn reference newValue : Data) (function : PV_THR2_OffPath.functionId fn=some 289) :
    value p c w fn [reference,newValue] = (do
      let address ← (runtime p).carrier.dereference w reference
      readAddress (runtime p).carrier c.store address) := by
  simp only [value,function]

theorem new_value (p : Parameters) (c : Config) (w : OWNER) (fn v : Data)
    (function : PV_THR2_OffPath.functionId fn=some 371) :
    value p c w fn [v] = some v := by simp only [value,function]

#print axioms value
#print axioms reply
#print axioms old_value
#print axioms new_value
end PV_LIB_SPEC_CellBindings13
