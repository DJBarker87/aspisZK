import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix010
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.encode_commitment_words_loop1.body`.
Recursive calls remain the original extracted calls. -/
def continueAfter (words : alloc.vec.Vec host_commitment.Word) (encoded : alloc.vec.Vec (core.result.Result host_commitment.Word
  aspis_core.r0.Error)) (out : Payload (alloc.vec.Vec.is_empty Global encoded)) : Result (ControlFlow ((alloc.vec.Vec host_commitment.Word) × (alloc.vec.Vec
    (core.result.Result host_commitment.Word aspis_core.r0.Error)))
    ((alloc.vec.Vec host_commitment.Word) × (Option (core.result.Result
    (alloc.vec.Vec host_commitment.Word) aspis_core.r0.Error)))) := do
  let b := out
  if b
  then ok (done (words, none))
  else
    let (o, encoded1) ← alloc.vec.Vec.pop Global encoded
    let r ← core.option.Option.unwrap o
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let words1 ← alloc.vec.Vec.push words val
      ok (cont (words1, encoded1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec host_commitment.Word) (core.convert.FromSame
          aspis_core.r0.Error) residual
      ok (done (words, some r1))


end R1Z.PV_RE_ComposedSuffix010
pv_composed_source_contexts ProverRwFull.host_commitment.encode_commitment_words_loop1.body
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix010.continueAfter
