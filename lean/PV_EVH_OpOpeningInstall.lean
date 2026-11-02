import PV_EVH_OpLeafInstall
import PV_EVH_OpPrepareOpening
import PV_EVH_FinishOpening
import PV_EVH_OpPublishCompact
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OpOpeningInstall
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes] [ExternalFuns]
/-- Install the three actual source spines. Their native callees, allocation,
formatting and observation fidelity remain explicit obligations. -/
def install (prepare : PV_EVH_OpPrepareOpening.Callees)
    (finish : PV_EVH_FinishOpening.Callees)
    (publish : PV_EVH_OpPublishCompact.Callees) : PV_EVH_OpLeafInstall.SemanticsCallees where
  prepare_opening_OPEN := fun variant hash backend sem =>
    PV_EVH_OpPrepareOpening.run variant hash backend sem prepare
  finish_opening_OPEN := fun variant hash prepared salts =>
    PV_EVH_FinishOpening.run variant hash prepared salts finish
  publish_compact_OPEN := fun variant p => PV_EVH_OpPublishCompact.run variant p publish

theorem install_fixed (prepare : PV_EVH_OpPrepareOpening.Callees)
    (finish : PV_EVH_FinishOpening.Callees) (publish : PV_EVH_OpPublishCompact.Callees)
    (hp : PV_EVH_OpPrepareOpening.Compatible prepare)
    (hf : PV_EVH_FinishOpening.Compatible finish)
    (hc : PV_EVH_OpPublishCompact.Compatible publish) :
    PV_EVH_OpLeafInstall.SemanticsCompatible (install prepare finish publish) where
  prepare_opening_fixed := fun variant hash backend sem =>
    PV_EVH_OpPrepareOpening.run_fixed variant hash backend sem prepare hp
  finish_opening_fixed := fun variant hash prepared salts =>
    PV_EVH_FinishOpening.run_fixed variant hash prepared salts finish hf
  publish_compact_fixed := fun variant p => PV_EVH_OpPublishCompact.run_fixed variant p publish hc
#print axioms install_fixed
end PV_EVH_OpOpeningInstall
