import AspisR1RhoResumeCaller.Funs
import CuSavingsCanonicalReader
import CuSavingsCanonicalKReader
import CuSavingsLibraOrigins
set_option autoImplicit false
namespace AspisR1RhoResumeCaller
open Aeneas Aeneas.Std Result ControlFlow
structure ResumeHeader where
  r : ResumeReader
  «end» : Usize
  state : Array U8 32#usize
  roots : Array (Array U8 32#usize) 2#usize

def retained_to_reader (r : ResumeReader) : AspisR1CanonicalReader.Reader := ⟨r.bytes,r.«at»⟩
def retained_from_reader (r : AspisR1CanonicalReader.Reader) : ResumeReader := ⟨r.bytes,r.«at»⟩
def retained_e (e : AspisR1CanonicalReader.field.wide_exact.WideExact) : aspis_core.field.WideExact :=
  ⟨⟨⟨e.c0.c0.a,e.c0.c0.b⟩,⟨e.c0.c1.a,e.c0.c1.b⟩⟩,⟨⟨e.c1.c0.a,e.c1.c0.b⟩,⟨e.c1.c1.a,e.c1.c1.b⟩⟩⟩
def retained_error (e : AspisR1CanonicalReader.Error) : verifier.Error :=
  match e with
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript | .Relation => .Relation
  | .Merkle => .Merkle | .Query => .Query | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def retained_read_e [AspisR1CanonicalReader.Runtime] (r : ResumeReader) :
    Result (core.result.Result aspis_core.field.WideExact verifier.Error × ResumeReader) := do
  let (v,after) ← AspisR1CanonicalReader.Reader.e (retained_to_reader r)
  .ok ((match v with | .Ok value => .Ok (retained_e value) | .Err error => .Err (retained_error error)),retained_from_reader after)

variable [AspisR1CanonicalReader.Runtime]
def retained_begin_fields
  (header : ResumeHeader) :
  Result (core.result.Result ResumeBegin verifier.Error)
  := do
  let (r, r1) ← retained_read_e header.r
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r2, r3) ← retained_read_e r1
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let (r4, r5) ← retained_read_e r3
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let (r6, r7) ← retained_read_e r5
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r6
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          ok (core.result.Result.Ok
            {
              r := r7,
              «end» := header.«end»,
              state := header.state,
              roots := header.roots,
              gamma := val,
              kappa := val1,
              alpha := (Array.make 2#usize [ val2, val3 ])
            })
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ResumeBegin (core.convert.FromSame verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ResumeBegin (core.convert.FromSame verifier.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ResumeBegin (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      ResumeBegin (core.convert.FromSame verifier.Error) residual


#print axioms retained_begin_fields
end AspisR1RhoResumeCaller
