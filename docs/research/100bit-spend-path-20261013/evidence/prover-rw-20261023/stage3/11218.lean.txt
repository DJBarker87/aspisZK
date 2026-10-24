import R1Z.ProverRwWireTypes
import R1Z.ProverRwWireFuns
import R1Z.ProverCommitSemanticProgram28
import R1Z.ProverCommitSemanticTransport26

/-! Exact nominal transport of the selected caller's validated block read.
No hash equation is assumed: the digest callback is the same on both sides.
Failure, divergence, row-order errors and the entire returned state are kept. -/
set_option autoImplicit false
namespace R1Z.ProverRwWireTransport
open Aeneas Aeneas.Std Result
open ProverCommitSemanticTransport26
abbrev NewState := ProverRwWire.host_wire.SemanticTranscript
abbrev OldState := AspisR1SimSemantic20.r1_wire.SemanticTranscript

def state {H : Type} (s : NewState H) : OldState H :=
  ⟨s.state,s.hash,s.next_row⟩

def error : ProverRwWire.r1_wire.Error → AspisR1SimSemantic20.r1_wire.Error
  | .Allocation => .Allocation
  | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow
  | .Tag r => .Tag r
  | .Length r => .Length r
  | .NonCanonical r v => .NonCanonical r v
  | .Boundary v => .Boundary v
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public
  | .ActivePole => .ActivePole

def result {A : Type} : core.result.Result A ProverRwWire.r1_wire.Error →
    core.result.Result A AspisR1SimSemantic20.r1_wire.Error
  | .Ok a => .Ok a
  | .Err e => .Err (error e)

def output {H A : Type}
    (v : core.result.Result A ProverRwWire.r1_wire.Error × NewState H) :=
  (result v.1,state v.2)

theorem sample {H : Type} (hash : ProverRwWire.aspis_core.digest.Digest32 H)
    (s : NewState H) (row : U8) (frame : Slice U8) :
    mapR output (ProverRwWire.host_wire.SemanticTranscript.sample_block_validated hash s row frame) =
      ProverCommitSemanticProgram28.sample hash.digest (state s) row frame := by
  simp only [ProverRwWire.host_wire.SemanticTranscript.sample_block_validated,
    ProverCommitSemanticProgram28.sample, state, map_bind,map_if,map_ok]
  rfl

#print axioms sample
end R1Z.ProverRwWireTransport
