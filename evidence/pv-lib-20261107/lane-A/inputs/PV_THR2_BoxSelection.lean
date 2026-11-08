import PV_THR2_BoxRegister
set_option autoImplicit false
noncomputable section
namespace PV_THR2_BoxSelection
open PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner
open PV_THR2_BoxRegister

/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
The generated result coordinate selects the pre-registration lifetime supply.
This is local bookkeeping; original-entry reachability remains open. -/
theorem place_selected {W : Type}
    (carrier : PV_STX2_Store.Carrier W PV_STX2_Syntax.Data)
    (c : PV_STX2_SliceMachine.Config) (w : W) (s : OWNER) :
    (register carrier c w s).places ⟨c.frame.activation,[45]⟩ = some s.next := by
  unfold register
  rw [PV_THR2_BoxOwnerPlace.source_place]
  exact (PV_EVHB_SourceLifetimes.constructor_receiver s _ shape 8).1

/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
The selected lifetime has the empty ThreadInit descriptor before allocation. -/
theorem header_selected {W : Type}
    (carrier : PV_STX2_Store.Carrier W PV_STX2_Syntax.Data)
    (c : PV_STX2_SliceMachine.Config) (w : W) (s : OWNER) :
    lookup (register carrier c w s).world s.next =
      some (PV_EVHB_SourceLifetimes.emptyHeader shape 8) := by
  unfold register
  rw [PV_THR2_BoxOwnerPlace.source_place]
  exact lookup_store _ _ _

#print axioms place_selected
#print axioms header_selected
end PV_THR2_BoxSelection
