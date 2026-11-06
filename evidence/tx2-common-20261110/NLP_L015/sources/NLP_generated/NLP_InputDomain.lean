import NLP_RootDomain
set_option autoImplicit false
noncomputable section
namespace NLP_InputDomain
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- A relation between the original checkpoint and proof inputs only.
It states no child Result or Merkle acceptance. Its external caller provenance
is OPEN; input lengths alone do not provide it. -/
def Root0 (ck proof : Slice U8) : Prop :=
 (ck.val.drop 112).take 32=(encodeState
  ((SemanticRecordCodec.decodeState (OraclePortCompactDraft.slice
   (MultiproofConeCanonical.bytesOf proof.val) 16 32)).getD (fun _=>0))).val
#print Root0
end NLP_InputDomain
