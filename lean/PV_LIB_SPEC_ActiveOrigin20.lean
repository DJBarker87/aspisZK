import PV_LIB_SPEC_ActivePoll20
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveOrigin20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_SPEC_ActivePoll20 (config wait request)

local instance : DecidableEq Site := Classical.decEq _

def origin (consumed : List Context) : Context :=
  ⟨PV_LIB_SPEC_TlsRequest15.site,
    (consumed.filter (fun (old : Context) => decide (old.site=PV_LIB_SPEC_TlsRequest15.site))).length,
    [PV_LIB_A_ActiveGetter17.init],PV_LIB_A_F5FullEntry16.activation,request⟩

theorem context (e : Entry) (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ResourceHistory.context (PV_LIB_SPEC_ActiveRequest20.after e issued consumed)
      config wait = some (origin consumed) := by
  classical
  simp [PV_LIB_SPEC_ResourceHistory.context,PV_LIB_SPEC_ActiveRequest20.after,
    PV_LIB_SPEC_TlsRequest15.after,config,wait,request,origin,
    PV_LIB_SPEC_ResourceHistory.arguments]

theorem away (e : Entry) (issued : List Issued) (consumed : List Context) :
    ¬ PV_LIB_A_ActiveEnvironment17.Corrected (PV_LIB_SPEC_ActiveRequest20.after e issued consumed).state := by
  apply PV_LIB_SPEC_ActiveAway20.token _ config wait (PV_LIB_SPEC_ActivePoll20.ordinary e issued consumed)
  intro s pointer eq
  have length := congrArg (fun req => (PV_LIB_SPEC_ResourceHistory.arguments req).length) eq
  change 1=2 at length
  omega

#print axioms origin
#print axioms context
#print axioms away
end PV_LIB_SPEC_ActiveOrigin20
