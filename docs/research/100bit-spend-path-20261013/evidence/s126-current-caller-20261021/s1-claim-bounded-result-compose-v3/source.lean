import S1ClaimDotBoundedResultV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.ClaimDotBoundedResult
def outerBody
  {D : Type} (ops : ClaimDotOps D)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (sem : r1_semantic.Verified H) (y1 : Slice Std.U8)
  (g : Array aspis_core.field.WideExact 29#usize)
  (k : Array aspis_core.field.WideExact 7#usize)
  (iter : core.ops.range.Range Std.Usize)
  (parts : Array aspis_core.field.WideExact 7#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.WideExact 7#usize)) (core.result.Result
    aspis_core.field.WideExact verifier.Error))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let we ← verifier.prepared_claim_sum k parts
    ok (done (core.result.Result.Ok we))
  | some point =>
    let r ← dot ops aspis_coreDigest32Inst sem y1 g point
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i ← point + 1#usize
      let a ← Array.update parts i val
      ok (cont (iter1, a))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.WideExact (core.convert.FromSame verifier.Error)
          residual
      ok (done r1)

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim]: loop 0:
    Source: 'lib.rs', lines 770:8-774:1 -/
def outerLoop
  {D : Type} (ops : ClaimDotOps D)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (iter : core.ops.range.Range Std.Usize) (sem : r1_semantic.Verified H)
  (y1 : Slice Std.U8) (g : Array aspis_core.field.WideExact 29#usize)
  (k : Array aspis_core.field.WideExact 7#usize)
  (parts : Array aspis_core.field.WideExact 7#usize) :
  Result (core.result.Result aspis_core.field.WideExact verifier.Error)
  := do
  loop
    (fun (iter1, parts1) => outerBody ops
      aspis_coreDigest32Inst sem y1 g k iter1 parts1)
    (iter, parts)

/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim]:
    Source: 'lib.rs', lines 767:0-774:1 -/
def claim
  {D : Type} (ops : ClaimDotOps D)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (sem : r1_semantic.Verified H) (y1 : Slice Std.U8)
  (inactive : aspis_core.field.WideExact)
  (g : Array aspis_core.field.WideExact 29#usize)
  (kappa : aspis_core.field.WideExact) :
  Result (core.result.Result aspis_core.field.WideExact verifier.Error)
  := do
  let k ← ops.powers 7#usize kappa
  let parts := Array.repeat 7#usize aspis_core.field.WideExact.ZERO
  let a ← Array.update parts 0#usize inactive
  outerLoop ops aspis_coreDigest32Inst
    { start := 0#usize, «end» := 6#usize } sem y1 g k a

/-- All branches and mutable parts updates of the actual retained outer body
are preserved; replacing the child introduces no child-success premise. -/
theorem outerBody_eq_source {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array aspis_core.field.WideExact 29#usize)
    (k : Array aspis_core.field.WideExact 7#usize) (iter : ClaimScalar.Range)
    (parts : Array aspis_core.field.WideExact 7#usize) :
    outerBody ops inst sem y1 g k iter parts =
      verifier.prepared_claim_loop.body ops inst sem y1 g k iter parts := by
  unfold outerBody verifier.prepared_claim_loop.body
  simp only [source_dot_eq_bounded]
  rfl

theorem outerLoop_eq_source {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (iter : ClaimScalar.Range)
    (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array aspis_core.field.WideExact 29#usize)
    (k : Array aspis_core.field.WideExact 7#usize)
    (parts : Array aspis_core.field.WideExact 7#usize) :
    outerLoop ops inst iter sem y1 g k parts =
      verifier.prepared_claim_loop ops inst iter sem y1 g k parts := by
  unfold outerLoop verifier.prepared_claim_loop
  simp only [outerBody_eq_source]

/-- COMPLETE enclosing claim Result equality, retaining the seven powers,
initial parts, all six dot calls, error propagation and final weighted sum.
No caller success, canonicality, parser success or arithmetic totality premise.
This is the retained extracted fission source, not yet the original nested
Rust source-to-fission equivalence. -/
theorem claim_eq_source {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (inactive : aspis_core.field.WideExact)
    (g : Array aspis_core.field.WideExact 29#usize) (kappa : aspis_core.field.WideExact) :
    claim ops inst sem y1 inactive g kappa =
      verifier.prepared_claim ops inst sem y1 inactive g kappa := by
  unfold claim verifier.prepared_claim
  simp only [outerLoop_eq_source]

#print axioms outerBody_eq_source
#print axioms outerLoop_eq_source
#print axioms claim_eq_source
end AspisR1CurrentPreparedClaim.ClaimDotBoundedResult
