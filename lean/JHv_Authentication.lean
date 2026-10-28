import JHv_Registry
import JHu_Authentication
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_Authentication
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2

/-- All seven original children on one dictionary and one corrected world.
No successful registry/decoder/PDA observation is retained as a hypothesis. -/
theorem source (base : Ops) (slot : U64) (runtime : FixturePdaRuntime base) :
    r1_pool_adapter.owned.authenticate_asq8_accounts
      (JHd_ReferenceSlots.install (JHv_Leaves.install base)) CPH_Program.verifier
      (JHg_World.e2.second S2W_D189Wrappers.secondSizes) JHb_Programs.pool 3#u8 slot=
        ok (.Ok JHg_AccountValues.value) := by
  exact JHu_Authentication.source
    (NCX_Install.install {NBX_SlotValues.instantiate base with op41:=ok JHv_Leaves.loader}) slot runtime
    (JHv_Registry.source base slot runtime)
#print axioms source
end AspisR1.JHv_Authentication
end
