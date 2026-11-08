import PV_LIB_A_BackingFrame9
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ThreadInitBacking9
open PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner
open PV_LIB_A_AllocationBacking9

/-- ThreadInit's source-selected local45 can belong to an older caller after
the Arc constructor returns. Numerical activation order is unnecessary: its
emitted local45 is structurally distinct from BoxNew's reserved ARG1 backing.
No equality of nextActivation across a caller boundary is imposed. -/
theorem registration (w : OWNER) (s : Store Data) (activation : Nat)
    (shape : R1Z.PV_FXM_ReserveWorld.Shape) (align id : Nat) (h : Header)
    (fresh : PV_EVHB_SourceLifetimes.Fresh w)
    (registered : w.places (PV_THR2_PacketBoxRegister.place s) = some id)
    (header : lookup w.world id = some h) :
    select (PV_EVHB_SourceLifetimes.newAt w ⟨activation,[45]⟩ shape align)
      (PV_THR2_PacketBoxBacking.root s) = some ⟨id,h⟩ := by
  have different : PV_THR2_PacketBoxRegister.place s ≠
      (⟨activation,[45]⟩ : PV_EVHB_OwnerMachine.Place) := by
    intro same
    have bad := congrArg PV_EVHB_SourceLifetimes.Place.fields same
    cases bad
  have prior : id ≠ w.next := Nat.ne_of_lt (fresh _ id registered)
  apply selected
  · change (if PV_THR2_PacketBoxRegister.place s = ⟨activation,[45]⟩ then _ else _) = _
    rw [if_neg different]
    exact registered
  · change lookup (store w.world w.next (PV_EVHB_SourceLifetimes.emptyHeader shape align)) id = _
    rw [lookup_other _ _ _ _ prior]
    exact header

#print axioms registration
end PV_LIB_A_ThreadInitBacking9
