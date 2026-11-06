import NLM_RowSpec_065
import NLM_Auth064Domain
set_option autoImplicit false
noncomputable section
namespace NLW_Root0
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.SqueezeOracleBridge
/-- Own-input checkpoint/proof relation, identical to the open common
caller's Root0 requirement. Lengths alone never establish this relation. -/
def Binds (checkpoint proof : Slice U8) : Prop :=
 (checkpoint.val.drop 112).take 32 = (encodeState
  ((SemanticRecordCodec.decodeState (OraclePortCompactDraft.slice
   (MultiproofConeCanonical.bytesOf proof.val) 16 32)).getD (fun _ => 0))).val
/-- Full common domain adds Root0 to the inherited size clauses. -/
def Domain {H : Type} (f : NLM_RowSpec_065.Frame H) : Prop :=
 NLM_RowSpec_065.Domain f ∧ Binds f.checkpoint f.proof
/-- Projection is one-way: the predecessor size-only domain is insufficient. -/
theorem sizes {H : Type} (f : NLM_RowSpec_065.Frame H) (h : Domain f) :
 NLM_RowSpec_065.Domain f := h.1
#print Binds
#print Domain
#print sizes
#print axioms sizes
end NLW_Root0
