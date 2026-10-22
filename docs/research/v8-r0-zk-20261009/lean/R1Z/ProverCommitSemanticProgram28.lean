import AspisR1SimSemantic20.Funs
import R1Z.ProverCommitStateLift28
/-! Generic monadic lift of the retained semantic caller. Pure validation
and decoding use the original retained functions. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSemanticProgram28
open Aeneas Aeneas.Std Result AspisR1SimSemantic20 ProverCommitStateLift28
variable {M : Type → Type} [Monad M] [MonadLiftT Result M]
def sample
  {H : Type} (effect : H → Parts → M Bytes32)
  (self : r1_wire.SemanticTranscript H) (row : Std.U8) (framed : Slice Std.U8)
  :
  M ((core.result.Result (Array Std.U8 32#usize) r1_wire.Error) ×
    (r1_wire.SemanticTranscript H))
  := do
  if row != self.next_row
  then
    pure (core.result.Result.Err (r1_wire.Error.RowOrder self.next_row row),
      self)
  else
    let s ← lift (Array.to_slice self.state)
    let i ← lift (Std.U8.wrapping_add 160#u8 row)
    let s1 ← lift (Array.to_slice (Array.make 2#usize [ 0#u8, i ]))
    let s2 ← lift (Array.to_slice (Array.make 3#usize [ s, s1, framed ]))
    let absorbed ← effect self.hash s2
    let s3 ← lift (Array.to_slice absorbed)
    let s4 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
    let s5 ← lift (Array.to_slice (Array.make 2#usize [ s3, s4 ]))
    let block ← effect self.hash s5
    let s6 ← lift (Array.to_slice absorbed)
    let s7 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
    let s8 ← lift (Array.to_slice (Array.make 2#usize [ s6, s7 ]))
    let a ← effect self.hash s8
    let i1 ← lift (Std.U8.wrapping_add self.next_row 1#u8)
    pure (core.result.Result.Ok block, { self with state := a, next_row := i1 })


def semantic
  {H : Type} (effect : H → Parts → M Bytes32)
  (state : r1_wire.SemanticTranscript H) (row : Std.U8)
  (record1 : alloc.vec.Vec Std.U8) :
  M ((core.result.Result aspis_core.field.QM31 r1_wire.Error) ×
    (r1_wire.SemanticTranscript H))
  := do
  if row > 24#u8
  then pure (core.result.Result.Err r1_wire.Error.InvalidRow, state)
  else
    if row != state.next_row
    then
      pure (core.result.Result.Err (r1_wire.Error.RowOrder state.next_row row),
        state)
    else
      let s := alloc.vec.Vec.deref record1
      let r ← r1_wire.semantic20.checked row s
      match r with
      | core.result.Result.Ok _ =>
        let s1 := alloc.vec.Vec.deref record1
        let (r1, state1) ←
          sample
            effect state row s1
        match r1 with
        | core.result.Result.Ok block =>
          let q ← AspisR1SimSemantic20.sampler.qm31_sample block
          pure (core.result.Result.Ok q, state1)
        | core.result.Result.Err e => pure (core.result.Result.Err e, state1)
      | core.result.Result.Err e => pure (core.result.Result.Err e, state)

end R1Z.ProverCommitSemanticProgram28
