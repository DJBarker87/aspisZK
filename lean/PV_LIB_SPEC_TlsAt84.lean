import PV_LIB_SPEC_TlsCallableHistory16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsAt84
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context initial)
open PV_LIB_SPEC_TlsAt75 (at75 store75 handler)
open PV_LIB_SPEC_TlsNative15 (cut reference)
open PV_LIB_SPEC_Tls75Cells16 (callable pointer)

def config : Config := PV_LIB_SPEC_TlsCallable16.config store75 5
  PV_LIB_SPEC_TlsOriginal15.parents PV_THR2_F2Call.descriptors.2 PV_LIB_SPEC_Entry13.slot.source
def at84 : Execution := PV_LIB_SPEC_SourceTransport15.advance
  PV_LIB_SPEC_ReachedEnvironment14.parameters handler 9 at75

theorem stage75 : at75 = PV_LIB_SPEC_F1Arithmetic14.stage store75 5
    PV_LIB_SPEC_TlsOriginal15.parents (PV_THR2_F170.live.body.drop 31)
    PV_LIB_SPEC_Entry14.state [] at75.issued at75.consumed := by
  calc at75 = ⟨at75.state,at75.issued,at75.consumed⟩ := rfl
       _ = _ := by rw [PV_LIB_SPEC_TlsAt75.state75]; rfl

theorem dereference :
    (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).carrier.dereference
      PV_LIB_SPEC_Entry14.state reference = some PV_LIB_SPEC_Entry13.slot.source := by
  simp only [reference,runtime,PV_THR2_OwnInitExactReturnedCases.carrier,
    PV_THR2_EntryDynamic.carrier,PV_THR2_Scalars.carrier,
    PV_STX2_TypedReferences.carrier,PV_STX2_TypedReferences.roundtrip]

theorem original84 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 84
      (initial PV_LIB_SPEC_Entry14.input) = at84 := by
  rw [show 84=75+9 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_TlsAt75.original75]
  unfold at84
  rw [stage75]
  exact PV_LIB_SPEC_SourceTransport15.run _ _ handler _ _
    (PV_LIB_SPEC_TlsCallable16.trace _ _ _ store75 5 PV_LIB_SPEC_TlsOriginal15.parents
      PV_LIB_SPEC_Entry14.state [] at75.issued at75.consumed _ reference _ callable pointer dereference)

theorem state84 : at84.state = ⟨⟨.running config,PV_LIB_SPEC_Entry14.state,[]⟩,[]⟩ := by
  unfold at84
  rw [PV_LIB_SPEC_SourceProjection15.state,PV_LIB_SPEC_TlsAt75.state75]
  exact PV_LIB_SPEC_TlsCallableLift16.source _ handler store75 5
    PV_LIB_SPEC_TlsOriginal15.parents _ reference _ PV_LIB_SPEC_Entry14.state [] callable pointer dereference

theorem issued84 : at84.issued =
    (⟨PV_LIB_SPEC_TlsCallableHistory16.site,5,
      .child PV_THR2_RunTlsCallable.descriptors.1 10
        [PV_THR2_F2Call.descriptors.2,PV_THR2_KeyValues.pack PV_THR2_RunTlsCallable.descriptors.2
          [reference]]⟩ : Issued) :: at75.issued := by
  unfold at84
  rw [stage75]
  exact PV_LIB_SPEC_TlsCallableHistory16.issued (cut ⟨0,0,⟨0,0,[]⟩,0⟩) _ handler store75 5
    PV_LIB_SPEC_TlsOriginal15.parents PV_LIB_SPEC_Entry14.state [] at75.issued at75.consumed
    _ reference _ callable pointer dereference

theorem consumed84 : at84.consumed = at75.consumed :=
  PV_LIB_SPEC_Tls279History16.consumed _ handler 9 at75

#print axioms config
#print axioms at84
#print axioms stage75
#print axioms dereference
#print axioms original84
#print axioms state84
#print axioms issued84
#print axioms consumed84
end PV_LIB_SPEC_TlsAt84
