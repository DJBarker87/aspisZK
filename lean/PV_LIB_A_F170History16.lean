import PV_LIB_A_ContextSource16
import PV_LIB_A_F170Result16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F170History16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_A_SourceSequence13

def after (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (stage (PV_LIB_A_F170Result16.stored PV_LIB_SPEC_Tls85Data16.store85 5 (.boolean false))
    5 PV_LIB_SPEC_TlsOriginal15.parents (PV_THR2_F170.live.body.drop 49)
    e.world [] [] []).state

theorem original94 (e : PV_LIB_SPEC_EntryWorld18.Entry) (activation : Nat) :
    (PV_LIB_SPEC_LaneAJoins18.history e activation 94).state = after e := by
  have value : PV_LIB_SPEC_Tls85Data16.store85.cells ⟨5,14,[]⟩ = some (.boolean false) := by
    simp [PV_LIB_SPEC_Tls85Data16.store85,write]
  have computed := PV_LIB_A_F170Result16.computed PV_LIB_SPEC_ReachedEnvironment14.parameters
    PV_LIB_SPEC_Tls85Data16.store85 5 (.boolean false) PV_LIB_SPEC_TlsOriginal15.parents e.world value
  let cut := PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e activation)
  let H : Handler := fun _ w => ⟨.pending,w,[]⟩
  let x := PV_LIB_SPEC_World18_Tls85Data16.at85 e
  have trace : PV_LIB_SPEC_SourceTransport15.Trace cut PV_LIB_SPEC_ReachedEnvironment14.parameters H 9 x := by
    change PV_LIB_SPEC_SourceTransport15.Trace cut _ H 9
      (stage PV_LIB_SPEC_Tls85Data16.store85 5 PV_LIB_SPEC_TlsOriginal15.parents
        (PV_THR2_F170.live.body.drop 40) e.world [] x.issued x.consumed)
    rw [← PV_LIB_A_F170Tail15.shape,← computed.1]
    exact PV_LIB_A_ContextSource16.trace cut _ H _ _ _ _ _ _ _ _ _ PV_LIB_A_F170Tail15.off
  have existing := PV_LIB_A_F170Tail15.run
    (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).carrier
    (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).control
    PV_LIB_SPEC_Full.programs PV_LIB_SPEC_ReachedEnvironment14.parameters.resources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.encode H
    (PV_LIB_SPEC_Values14.values PV_LIB_SPEC_ReachedEnvironment14.parameters)
    PV_LIB_SPEC_Tls85Data16.store85 5 PV_LIB_SPEC_TlsOriginal15.parents
    e.world [] []
  have transport := PV_LIB_A_V2TraceTransport14.run
    (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).carrier
    (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).control
    PV_LIB_SPEC_Full.programs PV_LIB_SPEC_ReachedEnvironment14.parameters.resources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.encode H
    (PV_LIB_SPEC_Values14.values PV_LIB_SPEC_ReachedEnvironment14.parameters)
    _ _ (PV_LIB_A_SourceSequence13.certified
      (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).carrier
      (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).control
      PV_LIB_SPEC_Full.programs H PV_LIB_A_F170Tail15.seq PV_LIB_SPEC_Tls85Data16.store85
      5 PV_LIB_SPEC_TlsOriginal15.parents [] (PV_THR2_F170.live.body.drop 49)
      e.world [] [] PV_LIB_A_F170Tail15.off).1
  rw [PV_LIB_A_F170Tail15.shape] at transport
  dsimp only at existing
  rw [transport,computed.1,computed.2] at existing
  change (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 94
    (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world))).state = _
  rw [show 94=85+9 from rfl,PV_LIB_SPEC_Original14.run_add,
    PV_LIB_SPEC_World18_TlsAt85.original85 e]
  exact PV_LIB_SPEC_SourceProjection15.transport cut _ H 9 x (after e) trace existing

#print axioms original94
end PV_LIB_A_F170History16
