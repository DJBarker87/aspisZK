import AspisR151QuerySchedule.Types
import AspisR136BeforeOod.FunsExternal
import AspisR137Q22.Funs
open Aeneas Aeneas.Std Result
namespace AspisR151QuerySchedule
abbrev aspis_core.field.QM31.write_le_bytes := AspisR136BeforeOod.aspis_core.field.QM31.write_le_bytes
abbrev aspis_core.transcript.Transcript.absorb := AspisR136BeforeOod.aspis_core.transcript.Transcript.absorb
abbrev aspis_core.transcript.Transcript.challenge_qm31 := AspisR136BeforeOod.aspis_core.transcript.Transcript.challenge_qm31
abbrev aspis_core.transcript.Transcript.challenge_nonzero_qm31 := AspisR136BeforeOod.aspis_core.transcript.Transcript.challenge_nonzero_qm31
def aspis_core.transcript.label.PROFILE : Result U8 := .ok AspisR137Transcript.transcript.label.PROFILE
def aspis_core.transcript.label.GRIND_NONCE : Result U8 := .ok 5#u8
def aspis_core.transcript.label.V6_FINAL256 : Result U8 := .ok 53#u8

def toQueryTranscript (t : aspis_core.transcript.Transcript) : AspisR137Q22.transcript.Transcript := ⟨t.state,t.hash⟩
def fromQueryTranscript (t : AspisR137Q22.transcript.Transcript) : aspis_core.transcript.Transcript := ⟨t.state,t.hash⟩
def aspis_core.transcript.Transcript.challenge_queries_without_replacement
    (t : aspis_core.transcript.Transcript) (count : Usize) (bound : U32) (maxDraws : Usize) :
    Result ((core.result.Result (alloc.vec.Vec U32) aspis_core.transcript.QuerySampleError) ×
      aspis_core.transcript.Transcript) := do
  let (r,next) ← AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement
    (toQueryTranscript t) count bound maxDraws
  .ok (r,fromQueryTranscript next)
end AspisR151QuerySchedule
