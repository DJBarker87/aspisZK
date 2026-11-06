import GExp_FirstCode
import NGP_L181
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Packets
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Complete external frame observed around the verifier call. Private owned
allocations may change; their physical admission/cleanup law is not inferred
from this record. Native relation instantiation must bind these byte values. -/
structure Frame094 where
 proof : Slice U8
 publicBytes : Slice U8
 externalBytes : Nat → List U8
 externalMetadata : Nat → List Nat
 authority : Nat → List U8
/-- Native invocation predicate supplied by the reviewed parent cut, never a
chosen child Result. This type is a required interface, not its realization. -/
abbrev Native094 :=
 (D : aspis_core.digest.Digest32 Unit) →
 (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) →
 (publicBytes proof : Slice U8) → Usize →
 Frame094 → Frame094 →
 NGP_L181.Observation (core.result.Result (alloc.vec.Vec U8) verifier.Error) → Prop
/-- Full parent-facing obligation under (be)(1). Native must be the ACTUAL
reviewed invocation relation; no theorem here installs or assumes a successful
native call. All k/proofs, inner Err, outer fail/div and chronological attempted
queries are quantified. Caller proves SAME-frame/input admission, not success.
The relation's physical carrier interpretation is deliberately an OPEN producer. -/
def RowSpec_094 (native : Native094) : Prop :=
 ∀ (base : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
 (std : ClaimsUnrolledFinish.StdCalls)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (D : aspis_core.digest.Digest32 Unit)
 (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize)
 (before after : Frame094)
 (observed : NGP_L181.Observation (core.result.Result (alloc.vec.Vec U8) verifier.Error)),
 before.proof = proof → before.publicBytes = publicBytes →
 native D public1 publicBytes proof k before after observed →
 NGP_L181.NativeAssociation hashv
   (NGQ_Normalize.normalize (GExp_FirstCode.code base B std hashv D public1 publicBytes proof k)) observed ∧
 after = before
#print RowSpec_094
end AspisR1.NLJ_Packets
end
