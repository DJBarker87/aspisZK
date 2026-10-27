import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix010
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


end R1Z.PV_RE_NoCatchSuffix010
pv_no_catch_binds ProverRwFull.host_commitment.encode_commitment_words_loop1.body
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix010.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix011
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.opening_lane_values`.
Recursive calls remain the original extracted calls. -/
def continueAfter (word : host_commitment.Word) (u : aspis_core.r0.domain.FibreIndex) (out : Payload (aspis_core.r0.domain.FibreIndex.get u)) : Result (Array aspis_core.field.wide_exact.WideExact 4#usize) := do
  let i := out
  let at1 ← Aeneas.Std.lift (Std.Usize.wrapping_mul 4#usize i)
  let we ← host_commitment.Word.value word at1
  let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 1#usize)
  let we1 ← host_commitment.Word.value word i1
  let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 2#usize)
  let we2 ← host_commitment.Word.value word i2
  let i3 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 3#usize)
  let we3 ← host_commitment.Word.value word i3
  ok (Array.make 4#usize [ we, we1, we2, we3 ])


end R1Z.PV_RE_NoCatchSuffix011
pv_no_catch_binds ProverRwFull.host_commitment.opening_lane_values
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix011.continueAfter
