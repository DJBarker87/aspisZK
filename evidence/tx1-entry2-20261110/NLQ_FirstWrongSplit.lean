import NLQ_WrongSplit
set_option autoImplicit false
noncomputable section
namespace NLQ_FirstWrongSplit
open Aeneas Aeneas.Std Result AspisR1 AspisR1CurrentCaller
/-- Complete first-decoded map-error suffix on a wrong split, including
handler fail/div. The SAME handler call is retained; there is no replacement
by an assumed successful InvalidInstructionData reply. -/
theorem fold (base : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
 (std : ClaimsUnrolledFinish.StdCalls) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (D : aspis_core.digest.Digest32 Unit)
 (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pub proof : Slice U8) (k : Usize) (bad : k≠compact.SPLIT)
 (handler : verifier.Error → Result AdapterRw.solana_program_error.ProgramError) :
 NGP_L181.NativeAssociation hashv
 (CheckpointBytes5Effect.bind
  (NGQ_Normalize.normalize (GExp_FirstCode.code base B std hashv D semantic pub proof k))
  (NLQ_FirstMap.continuation handler))
 (NLQ_FirstMap.observed handler ⟨.ok (.Err verifier.Error.Parse),[]⟩) := by
 exact NLQ_FirstMap.fold hashv _ handler _
  (NLQ_WrongSplit.child base B std hashv D semantic pub proof k bad)
#print fold
#print axioms fold
end NLQ_FirstWrongSplit
