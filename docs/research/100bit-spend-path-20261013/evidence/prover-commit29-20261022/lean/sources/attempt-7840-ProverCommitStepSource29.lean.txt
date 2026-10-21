import AspisR1SimSemantic20.Funs
import AspisR1SimControl21.Types
/-! Extracted one-step owner. All extracted semantic dependencies match the
retained namespace; only the verifier Error type is identified nominally. -/
set_option autoImplicit false
namespace AspisR1SimSemantic20
open Aeneas Aeneas.Std Result
def sim.owned29.semantic_step
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (st : r1_wire.SemanticTranscript H) (row : Std.U8)
  (record1 : alloc.vec.Vec Std.U8) (sem : Array aspis_core.field.QM31 25#usize)
  :
  Result (core.result.Result ((r1_wire.SemanticTranscript H) × (Array
    aspis_core.field.QM31 25#usize)) AspisR1SimControl21.verifier.Error)
  := do
  let (value, st1) ←
    r1_wire.semantic20.semantic aspis_coredigestDigest32Inst st row record1
  match value with
  | core.result.Result.Ok value1 =>
    let i ← lift (UScalar.cast .Usize row)
    let sem1 ← Array.update sem i value1
    ok (core.result.Result.Ok (st1, sem1))
  | core.result.Result.Err _ =>
    ok (core.result.Result.Err AspisR1SimControl21.verifier.Error.Semantic)

end AspisR1SimSemantic20
