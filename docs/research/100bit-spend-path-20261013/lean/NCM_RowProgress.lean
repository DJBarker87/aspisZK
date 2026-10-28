import NCE_RowObservations
import NCE_VerifierCuts

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_RowProgress
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts NCE_CarrierEffects
open MultiproofConeNodeDomain MultiproofConePhysicalTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev model : Node := fun caller physical i w =>
  annotate rowScratch caller (transport (MultiproofConePhysicalProgram.node caller.scratch physical i w))

/-- Progress and caller identity are DERIVED from the same one-row observation.
No successful row or next invariant is a hypothesis. -/
theorem progress {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input = ok (rawOracle H input))
    (native : Node) (cut : NCE_Native_Row H native)
    (caller : Carrier) (physical : Slice U8) (i w : Usize)
    (size : physical.val.length ≤ 5504) (domain : RowDomain physical caller.scratch i w)
    (active : i.val < caller.scratch.n.val) :
    ∃ out log, eval H (native caller physical i w) =
      (log,(ok out,{caller with scratch:=rowScratch caller.scratch (ok out),log:=caller.log++log})) ∧
      Progress physical caller.scratch i w out := by
  obtain ⟨out,returned,post⟩ := binary_step_progress D hash
    (fun input => ⟨rawOracle H input,law input⟩) physical caller.scratch i w domain active
  have result : (eval H (transport (MultiproofConePhysicalProgram.node caller.scratch physical i w))).2 = ok out := by
    rw [transport_observation]
    exact (MultiproofConePhysicalProgram.node_result D hash (rawOracle H) law _ _ _ _).trans returned
  refine ⟨out,(eval H (transport (MultiproofConePhysicalProgram.node caller.scratch physical i w))).1,?_,post⟩
  simp only [cut caller physical i w size domain active,annotate_eval,result]

#print axioms progress
end AspisR1.NCM_RowProgress
end
