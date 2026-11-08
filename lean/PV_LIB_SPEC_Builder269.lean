import PV_LIB_SPEC_Success13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Builder269
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
def nameKind : Data := .object [("Adt", (.array [(.object [("id", (.object [("Adt", (.number 17))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Adt", (.object [("id", (.object [("Adt", (.number 84))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.number 0), (.null)]))]
def sizeKind : Data := .object [("Adt", (.array [(.object [("id", (.object [("Adt", (.number 17))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Literal", (.object [("UInt", (.atom "Usize"))]))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.number 0), (.null)]))]
def builderKind : Data := .object [("Adt", (.array [(.object [("id", (.object [("Adt", (.number 95))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.null), (.null)]))]
/-- Exact269 source10000/10002/10003: None name, None size, no_hooks=false.
The false flag is important: the ORIGINAL default Builder DOES invoke454.
This is a source-value binding, not proof that454 has been executed. -/
def value : Data := PV_THR2_KeyValues.pack builderKind
  [PV_THR2_KeyValues.pack nameKind [],PV_THR2_KeyValues.pack sizeKind [],.boolean false]
def reply (w : OWNER) (r : Reply OWNER Event Data) : Reply OWNER Event Data :=
  match r.answer with
  | .returned (.ok _) => ⟨.returned (.ok value),w,r.events⟩
  | _ => {r with world := w}

theorem fields (p : Parameters) :
    (runtime p).carrier.field value 0 = some (PV_THR2_KeyValues.pack nameKind []) ∧
    (runtime p).carrier.field value 1 = some (PV_THR2_KeyValues.pack sizeKind []) ∧
    (runtime p).carrier.field value 2 = some (.boolean false) := ⟨rfl,rfl,rfl⟩
theorem absent (p : Parameters) :
    (runtime p).control.variant (PV_THR2_KeyValues.pack nameKind []) = some 0 ∧
    (runtime p).control.variant (PV_THR2_KeyValues.pack sizeKind []) = some 0 := ⟨rfl,rfl⟩
theorem frame (w : OWNER) (r : Reply OWNER Event Data) :
    (reply w r).world = w ∧ (reply w r).events = r.events := by
  rcases r with ⟨answer,after,events⟩
  cases answer with
  | pending => exact ⟨rfl,rfl⟩
  | fault f => exact ⟨rfl,rfl⟩
  | returned result => cases result <;> exact ⟨rfl,rfl⟩
#print axioms nameKind
#print axioms sizeKind
#print axioms builderKind
#print axioms value
#print axioms reply
#print axioms fields
#print axioms absent
#print axioms frame
end PV_LIB_SPEC_Builder269
