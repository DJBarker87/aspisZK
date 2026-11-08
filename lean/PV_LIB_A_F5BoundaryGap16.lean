import PV_LIB_A_F5Call16
import PV_LIB_A_C18_A_V2TableCongruence15
import PV_THR2_ActiveChild
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F5BoundaryGap16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_THR2_SourceStoreLibrary

def boundaryPrograms := PV_THR2_ActiveChild.table PV_LIB_SPEC_Full.programs

theorem full_lookup : PV_LIB_SPEC_Full.programs PV_THR2_ActivePrefix.descriptors.1 =
    some PV_THR2_F17.live := rfl

theorem boundary_lookup : boundaryPrograms PV_THR2_ActivePrefix.descriptors.1 = none :=
  PV_THR2_ActiveChild.child PV_LIB_SPEC_Full.programs

theorem no_agreement (e : PV_LIB_SPEC_EntryWorld18.Entry) (a : Nat) :
    ¬ PV_LIB_A_V2TableCongruence15.Agree PV_LIB_SPEC_Full.programs boundaryPrograms
      (PV_LIB_SPEC_LaneAJoins18.history e a 132).state := by
  rw [PV_LIB_A_F5Call16.original132]
  intro same
  let c := PV_THR2_ActiveRequest.pending PV_LIB_A_F5History16.store PV_LIB_A_F5History16.activation
    PV_LIB_A_F5History16.parents PV_LIB_SPEC_ReachedEnvironment14.parameters.needsDrop
  let wait : PV_STX2_Native.Waiting Data :=
    ⟨.child PV_THR2_ActivePrefix.descriptors.1 PV_LIB_A_F5History16.store.nextActivation
      [PV_STX2_TypedReferences.reference ⟨PV_LIB_A_F5History16.activation,3,[]⟩ .null,
       PV_THR2_KeyValues.pack PV_THR2_ActivePrefix.descriptors.2 []],
      .child PV_LIB_A_F5History16.store.nextActivation (.local 1),[]⟩
  have gap := same c rfl wait PV_THR2_ActivePrefix.descriptors.1 _ _ rfl rfl rfl
  rw [full_lookup,boundary_lookup] at gap
  cases gap

/-- The finite agreement certificate is refuted AT THE ACTUAL ORIGINAL request,
not postulated or tested on a fresh internal f5 start. -/
theorem no_trace (e : PV_LIB_SPEC_EntryWorld18.Entry) (a : Nat)
    (C : Carrier OWNER Data) (K : Control) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (n : Nat) :
    ¬ PV_LIB_A_V2TableCongruence15.Trace C K PV_LIB_SPEC_Full.programs boundaryPrograms
      resources encode H values (n+1) (PV_LIB_SPEC_LaneAJoins18.history e a 132).state := by
  intro trace
  exact no_agreement e a trace.1

#print axioms full_lookup
#print axioms boundary_lookup
#print axioms no_agreement
#print axioms no_trace
end PV_LIB_A_F5BoundaryGap16
