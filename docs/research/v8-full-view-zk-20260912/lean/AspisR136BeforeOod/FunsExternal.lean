import Aeneas.Std
import AspisR136BeforeOod.Types
import AspisR137Transcript.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR136BeforeOod

def toR137CM31 (x : aspis_core.field.CM31) :
    AspisR137Transcript.field.CM31 :=
  { a := x.a, b := x.b }

def toR137QM31 (x : aspis_core.field.QM31) :
    AspisR137Transcript.field.QM31 :=
  { c0 := toR137CM31 x.c0, c1 := toR137CM31 x.c1 }

def fromR137CM31 (x : AspisR137Transcript.field.CM31) :
    aspis_core.field.CM31 :=
  { a := x.a, b := x.b }

def fromR137QM31 (x : AspisR137Transcript.field.QM31) :
    aspis_core.field.QM31 :=
  { c0 := fromR137CM31 x.c0, c1 := fromR137CM31 x.c1 }

def mapChallenge
    (r : core.result.Result AspisR137Transcript.field.QM31
      AspisR137Transcript.transcript.ChallengeSampleExhausted) :
    core.result.Result aspis_core.field.QM31
      aspis_core.transcript.ChallengeSampleExhausted :=
  match r with
  | .Ok x => .Ok (fromR137QM31 x)
  | .Err e => .Err e

def aspis_core.field.QM31.write_le_bytes
    (self : aspis_core.field.QM31) (out : Slice Std.U8) :
    Result (Slice Std.U8) :=
  AspisR137Transcript.field.QM31.write_le_bytes (toR137QM31 self) out

def aspis_core.transcript.label.PROFILE : Result Std.U8 :=
  ok AspisR137Transcript.transcript.label.PROFILE

def aspis_core.transcript.label.STATEMENT : Result Std.U8 :=
  ok AspisR137Transcript.transcript.label.STATEMENT

def aspis_core.transcript.label.ROOT : Result Std.U8 :=
  ok AspisR137Transcript.transcript.label.ROOT

def aspis_core.transcript.label.SECOND_PHASE_ROOT : Result Std.U8 :=
  ok AspisR137Transcript.transcript.label.SECOND_PHASE_ROOT

def aspis_core.transcript.label.V6_POINT_CLAIMS : Result Std.U8 :=
  ok AspisR137Transcript.transcript.label.V6_POINT_CLAIMS

def aspis_core.transcript.Transcript.new
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) :
    Result aspis_core.transcript.Transcript :=
  AspisR137Transcript.transcript.Transcript.new hash

def aspis_core.transcript.Transcript.absorb
    (self : aspis_core.transcript.Transcript) (label : Std.U8)
    (data : Slice Std.U8) : Result aspis_core.transcript.Transcript :=
  AspisR137Transcript.transcript.Transcript.absorb self label data

def aspis_core.transcript.Transcript.challenge_qm31
    (self : aspis_core.transcript.Transcript) :
    Result ((core.result.Result aspis_core.field.QM31
      aspis_core.transcript.ChallengeSampleExhausted) ×
      aspis_core.transcript.Transcript) := do
  let (r, next) ← AspisR137Transcript.transcript.Transcript.challenge_qm31 self
  ok (mapChallenge r, next)

def aspis_core.transcript.Transcript.challenge_nonzero_qm31
    (self : aspis_core.transcript.Transcript) :
    Result ((core.result.Result aspis_core.field.QM31
      aspis_core.transcript.ChallengeSampleExhausted) ×
      aspis_core.transcript.Transcript) := do
  let (r, next) ←
    AspisR137Transcript.transcript.Transcript.challenge_nonzero_qm31 self
  ok (mapChallenge r, next)

theorem to_from_qm31 (x : AspisR137Transcript.field.QM31) :
    toR137QM31 (fromR137QM31 x) = x := by
  cases x with
  | mk c0 c1 => cases c0; cases c1; rfl

theorem from_to_qm31 (x : aspis_core.field.QM31) :
    fromR137QM31 (toR137QM31 x) = x := by
  cases x with
  | mk c0 c1 => cases c0; cases c1; rfl

#print axioms to_from_qm31
#print axioms from_to_qm31

end AspisR136BeforeOod
