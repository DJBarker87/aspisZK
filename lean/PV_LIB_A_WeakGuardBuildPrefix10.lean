import PV_LIB_A_WeakGuardBuildRun10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakGuardBuildPrefix10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_WeakGuardBuild10

/-- Actual584's complete guard-construction prefix on the repaired machine.
The provider representation premise is internal at this destructor entry;
this theorem does not claim the original caller has reached that entry. -/
theorem run (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (types : List Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (root slot : Nat) (ptr : Data) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (older : root ≠ a)
    (source : s.cells ⟨root,slot,[]⟩ = some
      (PV_THR2_Packet315SourceReturn.value ptr PV_THR2_Packet218ReturnData.allocator))
    (n : Nat) (bound : n ≤ 8) :
    PV_LIB_A_WeakGuardPrefix10.advance (PV_LIB_A_WeakOwnerFree10.step
      (PV_THR2_OwnInitExactReturnedCases.carrier C b) K P resources encode H values) n
      ⟨⟨⟨.running (configuration types s a parents root slot ptr 0),w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running (configuration types s a parents root slot ptr n),w,es⟩,stack⟩,none⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [PV_LIB_A_WeakGuardPrefix10.advance,ih (by omega)]
    exact PV_LIB_A_WeakGuardBuildRun10.corrected_step C K b P resources encode H values
      types s a parents root slot ptr w es stack older source n (by omega)

#print axioms run
end PV_LIB_A_WeakGuardBuildPrefix10
