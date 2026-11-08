import PV_LIB_SPEC_Active27920
import PV_LIB_SPEC_Tls279History16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Active279Issue20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

theorem run (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (address : Address)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (cell : s.cells ⟨a,5,[]⟩ = some (PV_LIB_SPEC_Tls278Values15.value address)) :
    PV_LIB_A_ActiveEnvironment17.run cut p 3
      (stage s a parents (PV_THR2_F170.live.body.drop 21) w es issued consumed) =
      PV_LIB_SPEC_Active27920.before s a parents address w es issued consumed := by
  rw [PV_LIB_SPEC_ActiveTrace20.run cut p H _ _
    (PV_LIB_SPEC_Tls279Request16.trace cut p H s a parents w es issued consumed)]
  refine PV_LIB_A_F170Return16.execution_ext
    (PV_LIB_SPEC_SourceTransport15.advance p H 3
      (stage s a parents (PV_THR2_F170.live.body.drop 21) w es issued consumed))
    (PV_LIB_SPEC_Active27920.before s a parents address w es issued consumed) ?_ ?_ ?_
  · rw [PV_LIB_SPEC_SourceProjection15.state]
    exact PV_LIB_SPEC_Tls279Request16.source p H s a parents
      (PV_LIB_SPEC_Tls278Values15.value address) w es cell
  · exact PV_LIB_SPEC_Tls279History16.issued p H s a parents
      (PV_LIB_SPEC_Tls278Values15.value address) w es issued consumed cell
  · exact PV_LIB_SPEC_Tls279History16.consumed p H 3 _

#print axioms run
end PV_LIB_SPEC_Active279Issue20
