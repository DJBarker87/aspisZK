import NDO_JHu_Master
import NDO_JHu_Checkpoint
import NDO_JHu_Lane
import NDO_JHu_PdaObservations
import NDO_JHj_Authentication
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHu_Authentication
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2

/-- Stage 1 partial composition. The registry child is explicitly still open;
this is not accepted2 and is not a SHA/runtime-only authentication theorem. -/
theorem source (base : Ops) (slot : U64) (runtime : FixturePdaRuntime base)
    (registry : r1_pool_adapter.owned.authenticate_invariant_release_registry
      (JHd_ReferenceSlots.install (NCV_Install.install base))
      CPH_Program.verifier JHb_Programs.pool (JHg_World.e2.snapshot 1 384 384)
      JHg_AccountValues.master (JHg_World.e2.snapshot 4 128 256)
      (JHg_World.e2.snapshot 5 192 320) slot=ok (.Ok ())) :
    r1_pool_adapter.owned.authenticate_asq8_accounts
      (JHd_ReferenceSlots.install (NCV_Install.install base)) CPH_Program.verifier
      (JHg_World.e2.second S2W_D189Wrappers.secondSizes) JHb_Programs.pool 3#u8 slot=
        ok (.Ok JHg_AccountValues.value) := by
  have retained : FixturePdaRuntime (NCV_Install.install base) := runtime
  exact JHj_Authentication.source (NCV_Install.install base) slot
    JHu_Master.observation (JHu_PdaObservations.master _ retained) registry
    JHu_Checkpoint.observation (JHu_PdaObservations.checkpoint _ retained)
    JHu_Lane.observation (JHu_PdaObservations.lane _ retained)
#print axioms source
end AspisR1.JHu_Authentication
end
