import NDO_JHv_RegistryCaller
import NDO_JHv_LeafObservations
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_Registry
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2

/-- The seventh original authentication child, with current model decoders
and the same four fixture PDA calls. Only the explicit runtime premise remains. -/
theorem source (base : Ops) (slot : U64) (runtime : FixturePdaRuntime base) :
    r1_pool_adapter.owned.authenticate_invariant_release_registry
      (JHd_ReferenceSlots.install (JHv_Leaves.install base)) CPH_Program.verifier JHb_Programs.pool
      (JHg_World.e2.snapshot 1 384 384) JHg_AccountValues.master
      (JHg_World.e2.snapshot 4 128 256) (JHg_World.e2.snapshot 5 192 320) slot=ok (.Ok ()) := by
  apply JHv_RegistryCaller.source (JHv_Leaves.install base) slot (JHv_Leaves.runtime base runtime)
  · exact JHv_LeafObservations.policy
  · change ok JHv_Leaves.loader=ok JHj_RegistryValue.loader
    exact congrArg ok JHv_Leaves.loader_fixture
  · exact NCX_JHuObservations.registry _
  · exact JHv_LeafObservations.immutable
  · exact JHv_LeafObservations.unrevoked
  · exact NCX_JHuObservations.entry _
  · exact JHv_LeafObservations.active slot
#print axioms source
end AspisR1.JHv_Registry
end
