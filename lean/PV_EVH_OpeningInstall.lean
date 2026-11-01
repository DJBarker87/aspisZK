import PV_EVH_LeafInstall
import PV_EVH_PrepareOpening
import PV_EVH_FinishOpening
import PV_EVH_PublishCompact
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OpeningInstall
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes] [ExternalFuns]
/-- Install the three actual source spines. Their native callees, allocation,
formatting and observation fidelity remain explicit obligations. -/
def install (prepare : PV_EVH_PrepareOpening.Callees)
    (finish : PV_EVH_FinishOpening.Callees)
    (publish : PV_EVH_PublishCompact.Callees) : PV_EVH_LeafInstall.SemanticsCallees where
  prepare_opening_OPEN := fun variant hash backend sem =>
    PV_EVH_PrepareOpening.run variant hash backend sem prepare
  finish_opening_OPEN := fun variant hash prepared salts =>
    PV_EVH_FinishOpening.run variant hash prepared salts finish
  publish_compact_OPEN := fun variant p => PV_EVH_PublishCompact.run variant p publish

theorem install_fixed (prepare : PV_EVH_PrepareOpening.Callees)
    (finish : PV_EVH_FinishOpening.Callees) (publish : PV_EVH_PublishCompact.Callees)
    (hp : PV_EVH_PrepareOpening.Compatible prepare)
    (hf : PV_EVH_FinishOpening.Compatible finish)
    (hc : PV_EVH_PublishCompact.Compatible publish) :
    PV_EVH_LeafInstall.SemanticsCompatible (install prepare finish publish) where
  prepare_opening_fixed := fun variant hash backend sem =>
    PV_EVH_PrepareOpening.run_fixed variant hash backend sem prepare hp
  finish_opening_fixed := fun variant hash prepared salts =>
    PV_EVH_FinishOpening.run_fixed variant hash prepared salts finish hf
  publish_compact_fixed := fun variant p => PV_EVH_PublishCompact.run_fixed variant p publish hc
#print axioms install_fixed
end PV_EVH_OpeningInstall
