import NLQ_FirstMap
set_option autoImplicit false
noncomputable section
namespace NLQ_FirstPacket
open Aeneas Aeneas.Std Result AspisR1 AspisR1CurrentCaller
open AspisR1.NLJ_Packets
/-- Parameterized digest/Result fold consuming the ORIGINAL RowSpec_094 at
SAME arguments. This is NOT a native parent row root: handler/error-allocation
frames and the physical parent cut remain to be installed and audited. -/
theorem fold (native : Native094) (childPacket : RowSpec_094 native)
 (base : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
 (std : ClaimsUnrolledFinish.StdCalls)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (D : aspis_core.digest.Digest32 Unit)
 (statement : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pub proof : Slice U8) (k : Usize) (pre post : Frame094)
 (child : NGP_L181.Observation (core.result.Result (alloc.vec.Vec U8) verifier.Error))
 (handler : verifier.Error → Result AdapterRw.solana_program_error.ProgramError)
 (proofInput : pre.proof=proof) (publicInput : pre.publicBytes=pub)
 (entered : native base B std hashv D statement pub proof k pre post child) :
 NGP_L181.NativeAssociation hashv
  (CheckpointBytes5Effect.bind
   (NGQ_Normalize.normalize (GExp_FirstCode.code base B std hashv D statement pub proof k))
   (NLQ_FirstMap.continuation handler)) (NLQ_FirstMap.observed handler child) ∧
 post=pre := by
 have packet := childPacket base B std hashv D statement pub proof k pre post child
  proofInput publicInput entered
 exact ⟨NLQ_FirstMap.fold hashv _ handler child packet.1,packet.2⟩
#check @fold
#print axioms fold
end NLQ_FirstPacket
