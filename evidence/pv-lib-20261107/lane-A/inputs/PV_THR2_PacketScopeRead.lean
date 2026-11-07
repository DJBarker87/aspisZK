import PV_THR2_Spawn361PacketField82Reached
set_option autoImplicit false
namespace PV_THR2_PacketScopeRead
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Exact next source13726 read. Hypotheses are the internal local28 reference
already derived from source13325. The arbitrary address is retained, and this
lemma adds no successful read or receiver premise. Conditional on amended
translator acceptance. -/
theorem read (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (w : OWNER)
    (a : Nat) (p : Address)
    (fieldCell : s.cells ⟨a,28,[]⟩ = some
      (PV_STX2_TypedReferences.reference {p with fields := p.fields ++ [0]} .null)) :
    PV_STX2_Store.read (PV_THR2_OwnInitExactReturnedCases.carrier C b) s w a
      (.project (.local 28) .deref) =
    (s.cells {p with fields := []}).bind
      (readFields (PV_THR2_OwnInitExactReturnedCases.carrier C b) (p.fields ++ [0])) := by
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have dereference : B.dereference w
      (PV_STX2_TypedReferences.reference {p with fields := p.fields ++ [0]} .null) =
      some {p with fields := p.fields ++ [0]} :=
    PV_STX2_TypedReferences.dereference _ _ _ _
  simp only [PV_STX2_Store.read,fieldCell,Option.bind_some]
  change (B.dereference w _).bind (readAddress B s) = _
  rw [dereference]
  rfl
/-- The precise remaining source read requirement is exposed, not installed as
a closure hypothesis. Arbitrary returned-reference representation alone gives
neither a root cell nor a field value. -/
theorem selected_iff (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (w : OWNER)
    (a : Nat) (p : Address) (value : Data)
    (fieldCell : s.cells ⟨a,28,[]⟩ = some
      (PV_STX2_TypedReferences.reference {p with fields := p.fields ++ [0]} .null)) :
    PV_STX2_Store.read (PV_THR2_OwnInitExactReturnedCases.carrier C b) s w a
      (.project (.local 28) .deref) = some value ↔
    ∃ root, s.cells {p with fields := []} = some root ∧
      readFields (PV_THR2_OwnInitExactReturnedCases.carrier C b) (p.fields ++ [0]) root = some value := by
  rw [read C b s w a p fieldCell]
  cases h : s.cells {p with fields := []} with
  | none => simp
  | some root => simp
#print axioms read
#print axioms selected_iff
end PV_THR2_PacketScopeRead
