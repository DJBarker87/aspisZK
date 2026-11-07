import PV_W5_F31Specification
import PV_STX2_CallSummaryAggregateRun
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31Carrier
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine

/-- AllocInit is already installed in the original source constructor table.
The own-entry wrapper therefore leaves the whole carrier unchanged. -/
theorem installed (base : Carrier PV_STX_World.World Data) (K : Control)
    (H : PV_W5_F35Modes.HType) :
    PV_STX2_Source7ConstructorEntry.carrier (PV_STX2_Source7QUniformReturnCompatibility.C base K H) =
    PV_STX2_Source7QUniformReturnCompatibility.C base K H := by
  let D := PV_STX2_Source7QUniformReturnCompatibility.C base K H
  have aggregate : (PV_STX2_Source7ConstructorEntry.carrier D).aggregate=D.aggregate := by
    funext tag values
    unfold PV_STX2_Source7ConstructorEntry.carrier
    dsimp only
    split
    · rename_i selected
      unfold PV_STX2_Source7ConstructorEntry.selects at selected
      split at selected
      · cases values <;> rfl
      · contradiction
    · rfl
  exact congrArg (PV_STX2_SliceAggregateExtension.extend D) aggregate

#print axioms installed
end PV_W5_F31Carrier
