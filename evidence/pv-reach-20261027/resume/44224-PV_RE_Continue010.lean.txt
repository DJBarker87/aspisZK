import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue010
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

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (words : alloc.vec.Vec host_commitment.Word) (encoded : alloc.vec.Vec (core.result.Result host_commitment.Word
  aspis_core.r0.Error)) :
    host_commitment.encode_commitment_words_loop1.body (words := words) (encoded := encoded) =
      (alloc.vec.Vec.is_empty Global encoded >>= fun out => continueAfter (words := words) (encoded := encoded) out) := by
  rw [host_commitment.encode_commitment_words_loop1.body]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (words : alloc.vec.Vec host_commitment.Word) (encoded : alloc.vec.Vec (core.result.Result host_commitment.Word
  aspis_core.r0.Error)) (out : Payload (alloc.vec.Vec.is_empty Global encoded))
    (h : (alloc.vec.Vec.is_empty Global encoded) = .ok out) :
    host_commitment.encode_commitment_words_loop1.body (words := words) (encoded := encoded) = continueAfter (words := words) (encoded := encoded) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (words : alloc.vec.Vec host_commitment.Word) (encoded : alloc.vec.Vec (core.result.Result host_commitment.Word
  aspis_core.r0.Error)) (e : Error)
    (h : (alloc.vec.Vec.is_empty Global encoded) = .fail e) :
    host_commitment.encode_commitment_words_loop1.body (words := words) (encoded := encoded) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (words : alloc.vec.Vec host_commitment.Word) (encoded : alloc.vec.Vec (core.result.Result host_commitment.Word
  aspis_core.r0.Error))
    (h : (alloc.vec.Vec.is_empty Global encoded) = .div) :
    host_commitment.encode_commitment_words_loop1.body (words := words) (encoded := encoded) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue010
