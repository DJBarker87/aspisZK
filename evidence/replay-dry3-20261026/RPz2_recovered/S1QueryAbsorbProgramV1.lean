import S1QueryModelContinuationV1
import ExtractedDigest32Callers
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

/-- Exact source framing, retaining the source's u32 cast of payload length.
The sole checked addition is discharged for actual query row31. -/
theorem query_absorb31_program {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (payload : Slice U8) :
    oracleProgram (PreparedHashEffects.absorb effects D self 31#u8 payload)=
      Program.ask (flatten (CallerStep.openingAbsorbParts self.state 191#u8
        (UScalar.cast .U32 (Slice.len payload)) payload))
        (fun state => .done (ok {self with state := encodeState state})) := by
  have tag : 160#u8 + 31#u8=ok 191#u8 := rfl
  unfold PreparedHashEffects.absorb
  simp only [oracleProgram_bind,oracleProgram_lift,oracleProgram_digest,oracleProgram_pure,
    tag,lift,AspisV8R19.OracleProgramOps.bind,continueOracle]
  rfl

#print axioms query_absorb31_program
end AspisR1PublicPreparation.PreparedHashCode
