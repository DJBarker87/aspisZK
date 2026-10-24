import S2W_ChildJoins
import S2W_TrustedStd
import S2W_OracleAudit

/-! Complete premise-shape audit for continuation2. The necessary-returning
result is about the exact existing leadDigest. It does not replace that
native dictionary by a total ideal dictionary or weaken Required14. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_ClosureAudit
open Aeneas Aeneas.Std Result
open S2LeadInterface S2Z.Oracle MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Total backend return is NECESSARY for the requested exact caller facts,
even if all native cuts and every child theorem have already been supplied.
This extracts a consequence; it is not a proposed extra premise or trust item. -/
theorem facts_require_backend_returns {Observer : Type} (ops : AdapterRw.Ops)
    (backend : Parts → Result Digest) (binding : NativeBinding ops backend)
    (c : Inputs Observer) (H : Bytes → State) (stored pub saved : Bytes) (parsed : Parsed)
    (facts : S2CallerFacts c (leadDigest ops) () H stored pub saved parsed) :
    ∀ parts, ∃ digest, backend parts = ok digest := by
  intro parts
  refine ⟨MultiproofConePhysicalTransport.rawOracle H parts, ?_⟩
  have total := facts.oracle parts
  change ops.op43 () parts = _ at total
  rw [binding] at total
  exact total

/-- A native backend nonreturn at ANY input excludes the exact total caller
field for that same dictionary. No claim is made that the deployed backend
has this behavior: the retained countermodel is a premise-strength audit. -/
theorem nonreturn_excludes_facts {Observer : Type} (ops : AdapterRw.Ops)
    (backend : Parts → Result Digest) (binding : NativeBinding ops backend)
    (blocked : Parts) (nonreturn : ¬ ∃ digest, backend blocked = ok digest)
    (c : Inputs Observer) (H : Bytes → State) (stored pub saved : Bytes) (parsed : Parsed) :
    ¬ S2CallerFacts c (leadDigest ops) () H stored pub saved parsed := by
  intro facts
  exact nonreturn (facts_require_backend_returns ops backend binding c H stored pub saved parsed facts blocked)

#print axioms facts_require_backend_returns
#print axioms nonreturn_excludes_facts
#print axioms S2W_ChildJoins.internal_geometry
#print axioms S2W_TrustedStd.specification_satisfies
#print axioms S2W_TrustedStd.cells_compose
#print axioms S2W_TrustedStd.accepted_copy
#print axioms S2W_TrustedStd.mismatched_copy
#print axioms S2W_TrustedStd.copy_frame
#print S2W_TrustedStd.TrustedStd
#print S2W_ChildJoins.FirstEntryVerifierConeJoin
#print S2W_ChildJoins.MultiproofConeJoin
#print S2W_ChildJoins.S8StageConeJoin
#print S2W_ChildJoins.S7StageConeJoin
#print S2W_ChildJoins.CheckpointConeJoin
#print S2W_ChildJoins.FullForestConeJoin
end AspisR1.S2W_ClosureAudit
end
