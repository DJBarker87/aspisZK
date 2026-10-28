import NCM_Tree
import NCM_NodeViews
import NCE_Statements

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_BatchTypes
open Aeneas Aeneas.Std Result NCE_OpeningCuts
open AspisV8R19.SqueezeOracleBridge

/-- Function data only. Native laws remain separate named theorem parameters;
this record does not bundle or discharge any proof obligation. -/
structure Ops where
  keys : NCM_KeysLeaves.Keys
  leaf : NCM_LeafLoop.Ops
  count : NCM_CountCarrier.Ops
  padding : NCE_PaddingCuts.Body Carrier
  verifier : NCM_Tail.Verifier
  start : NCE_OuterCuts.Start
  after0 : NCE_OuterCuts.Continue
  after1 : NCE_OuterCuts.Continue
  finish : NCE_OuterCuts.Finish
  rowStore : NCE_RowStoreCuts.Store
  valueSort : NCE_SortCuts.Step

/-- Input provenance only: original proof, actual Prepared queries/two roots
and the actual folded-root argument. No execution result or child output is
included. The enclosing U00/prepare/resume caller must establish these facts. -/
structure Inputs (s : Carrier) (parsed : OraclePortCompactDraft.Parsed)
    (folded : NCE_VerifierCuts.Digest) : Prop where
  proofLength : s.proof.val.length = 57607
  wire : parsed.wire = MultiproofConeCanonical.bytesOf s.proof.val
  queries : ∀ j, j < 22 → s.prepared.queries.val[j]!.val < 262144
  root0 : Port3_BatchStage.root0 s.prepared = encodeState (OraclePortBatchDraft.committedRoot parsed 0)
  root1 : Port3_BatchStage.root1 s.prepared = encodeState (OraclePortBatchDraft.committedRoot parsed 1)
  root2 : folded = encodeState (OraclePortBatchDraft.committedRoot parsed 2)

def root (s : Carrier) (folded : NCE_VerifierCuts.Digest) (kind : Nat) : NCE_VerifierCuts.Digest :=
  if kind=0 then Port3_BatchStage.root0 s.prepared
  else if kind=1 then Port3_BatchStage.root1 s.prepared else folded

def Good (original current : Carrier) : Prop := current.prepared=original.prepared ∧ current.proof=original.proof

/-- Actual root projection from the SAME Prepared/folded argument. -/
theorem root_value (s current : Carrier) (parsed : OraclePortCompactDraft.Parsed)
    (folded : NCE_VerifierCuts.Digest) (inputs : Inputs s parsed folded)
    (good : Good s current) (kind : Nat) (bound : kind < 3) :
    root current folded kind = encodeState (OraclePortBatchDraft.committedRoot parsed kind) := by
  interval_cases kind <;> simp [root,good.1,inputs.root0,inputs.root1,inputs.root2]

#print axioms root_value
end AspisR1.NCM_BatchTypes
end
