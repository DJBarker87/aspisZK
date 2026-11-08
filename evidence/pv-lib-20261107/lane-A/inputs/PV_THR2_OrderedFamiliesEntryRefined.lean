import PV_EVHB_OrderedFamiliesEntry
import PV_THR2_OwnInitExactReturnedCases
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OrderedFamiliesEntryRefined
open PV_EVHB_OwnerMachine PV_EVHB_OrderedFamiliesEntry
open PV_STX2_Syntax PV_STX2_Store
/-- Thread-10: the caller's closure field zero is the reference to the same
entry-owned F region. The source address names that region's entry-selected
OWNER place, whose identity is registered. The remaining fields stay arbitrary.
No run, receiver selection, later configuration or output occurs here. -/
def CaptureAt (s : OWNER) (p : Places) (closure : Data) : Prop :=
  ∃ (kind : Data) (rest : List Data) (address : Address) (id : Nat),
    p.f = ⟨address.activation,address.localIndex :: address.fields⟩ ∧
    s.places p.f = some id ∧
    closure = PV_THR2_KeyValues.pack kind
      (PV_STX2_TypedReferences.reference address .null :: rest)
/-- Thread-10 refinement of the named caller obligation. Exactly the old
entry storage plus the captured field's address, registration and representation.
The caller still discharges the same original-entry obligation. -/
def OrderedFamiliesEntryOwned' {F Task : Type} (s : OWNER)
    (c : Captures F Task) (closure : Data) : Prop :=
  ∃ p : Places, At s c p ∧ CaptureAt s p closure
/-- Hypothesis: the refined entry obligation; conclusion: the old obligation. -/
theorem old {F Task : Type} (s : OWNER) (c : Captures F Task) (closure : Data)
    (entry : OrderedFamiliesEntryOwned' s c closure) : OrderedFamiliesEntryOwned s c := by
  obtain ⟨p,owned,_⟩ := entry
  exact ⟨p,owned⟩
/-- Hypothesis: the refined entry obligation only. The captured source address
and registered identity are entry witnesses, independent of any later world. -/
theorem selection {F Task : Type} (s : OWNER) (c : Captures F Task) (closure : Data)
    (entry : OrderedFamiliesEntryOwned' s c closure)
    (C : Carrier OWNER Data) (b : Bool) (w : OWNER) :
    ∃ (p : Places) (address : Address) (id : Nat), At s c p ∧
      p.f = ⟨address.activation,address.localIndex :: address.fields⟩ ∧
      s.places p.f = some id ∧
      ((PV_THR2_OwnInitExactReturnedCases.carrier C b).field closure 0 >>=
        (PV_THR2_OwnInitExactReturnedCases.carrier C b).dereference w) = some address := by
  obtain ⟨p,owned,kind,rest,address,id,place,registered,shape⟩ := entry
  refine ⟨p,address,id,owned,place,registered,?_⟩
  rw [shape]
  have field : (PV_THR2_OwnInitExactReturnedCases.carrier C b).field
      (PV_THR2_KeyValues.pack kind
        (PV_STX2_TypedReferences.reference address .null :: rest)) 0 =
      some (PV_STX2_TypedReferences.reference address .null) := rfl
  rw [field]
  change (PV_THR2_OwnInitExactReturnedCases.carrier C b).dereference w
    (PV_STX2_TypedReferences.reference address .null) = some address
  exact PV_STX2_TypedReferences.dereference _ _ _ _
#print axioms old
#print axioms selection
end PV_THR2_OrderedFamiliesEntryRefined
