import NLQ_FirstPacket
set_option autoImplicit false
noncomputable section
namespace NLQ_WrongSplit
open Aeneas Aeneas.Std Result AspisR1 AspisR1CurrentCaller
/-- The source's split guard returns Parse BEFORE all parser/digest/field
calls, for every public/proof input. In particular eleven is not discarded
by the enclosing account guards; it reaches this rejection if they return. -/
theorem code (base : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
 (std : ClaimsUnrolledFinish.StdCalls) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (D : aspis_core.digest.Digest32 Unit)
 (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pub proof : Slice U8) (k : Usize) (bad : k≠compact.SPLIT) :
 GExp_FirstCode.code base B std hashv D semantic pub proof k=
 CheckpointBytes5Effect.Code.done (.Err verifier.Error.Parse) := by
 simp [GExp_FirstCode.code,bad]
/-- Complete attempted digest history is EMPTY, not a success-only trace. -/
theorem child (base : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
 (std : ClaimsUnrolledFinish.StdCalls) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (D : aspis_core.digest.Digest32 Unit)
 (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pub proof : Slice U8) (k : Usize) (bad : k≠compact.SPLIT) :
 NGP_L181.NativeAssociation hashv
 (NGQ_Normalize.normalize (GExp_FirstCode.code base B std hashv D semantic pub proof k))
 ⟨.ok (.Err verifier.Error.Parse),[]⟩ := by
 rw [code base B std hashv D semantic pub proof k bad]
 rfl
#print code
#print axioms code
#print axioms child
end NLQ_WrongSplit
