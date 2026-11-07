import NLQ_FirstPacket
import NLQ_ErrorMapper
import NLF_SdkBorrowLaw
set_option autoImplicit false
noncomputable section
namespace NLQ_FirstState
open Aeneas Aeneas.Std Result AspisR1 AspisR1CurrentCaller AspisR1.NLJ_Packets
/-- One parent state for TX1:328. The SDK state remains the SAME input across
the owned verifier/error calls; proving that frame natively is still required. -/
structure State where
 external : Frame094
 sdk : NLF_SdkModel.State
 errorLog : List String
 allocations : List (alloc.vec.Vec U8)
inductive Event where
 | observer (pre post : State)
 | child (pre post : State) (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
   (publicBytes proof : Slice U8) (k : Usize)
   (reply : Result (core.result.Result (alloc.vec.Vec U8) verifier.Error))
   (attempted : SdkC_Source.Log)
 | errorMap (pre post : State) (error : verifier.Error)
   (reply : Result AdapterRw.solana_program_error.ProgramError)
