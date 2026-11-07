import LIBB_PoolReconstruct
import LIBB_ObservationMap
set_option autoImplicit false
noncomputable section
namespace LIBB_ReconstructGraph
open Aeneas Aeneas.Std RSL
open LIBB_PoolCarriers
/-- Full graph-of-model characterization, including exactly the named
reconstruction Box prefix. The two silent allocation sites share a prefix. -/
theorem exact_graph (q : Request) (a : LIBB_AuthCarrier.Raw) (c : Afterstate)
 (env : Env) (o : Obs (Except ProgramError Statement)) :
 LIBB_PoolReconstruct.reconstruct q (NND_Carrier.auth a) c env o ↔
 o = LIB_Carriers.resultObs LIBB_PoolReconstruct.reply []
       (AspisR1.NFY_JHf_ReconstructionSlot.source q a c) ∨
 (NMS_R2N_ReconstructSites.reaches_boxes q a c ∧ o = ⟨.abort,[]⟩) := by
 rw [LIBB_PoolReconstruct.same_input]
 unfold NMS_R2N_ReconstructSites.meaning
 split
 · rw [LIBB_ObservationMap.two_alloc_graph]
   simp only [‹NMS_R2N_ReconstructSites.reaches_boxes q a c›,true_and]
 · rw [LIBB_ObservationMap.lift_graph]
   simp only [‹¬NMS_R2N_ReconstructSites.reaches_boxes q a c›,false_and,or_false]
#print axioms exact_graph
end LIBB_ReconstructGraph
end
