import ExtractedFirstCallerReachability

/-! Observer-off caller interpretation. Decoder/selector carriers and downstream
functions have exactly the explicit boundary status of the historical caller.
No SDK or downstream verifier totality is inferred. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S2ObserverOff
open AspisR1PublicPreparation
open AspisR1PublicPreparation.FirstCaller
open AspisR1PublicPreparation.PreparationBinding

/-- Frozen default-feature observer; no callback can run. -/
def observer : Result (Option (Phase → Result Unit)) := do
  ok none

/-- Frozen split-out downstream call with its explicit boundary interpreter. -/
def first_decoded {E F : Type}
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E) (selected : Public)
    (public_bytes proof : Slice U8) (k : Usize) :
    Result (core.result.Result (alloc.vec.Vec U8) E) := do
  let obs ← observer
  let r ← tx1 selected public_bytes proof k () obs
  core.result.Result.map_err (BuiltinFnOnce F E) r error

/-- Frozen decoding prefix, calling the split-out function. -/
def first {E F : Type} (invalidAccountData : E)
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E) (public_bytes proof : Slice U8) (k : Usize) :
    Result (core.result.Result (alloc.vec.Vec U8) E) := do
  let r ← decode public_bytes
  let r1 ← core.result.Result.map_err (decodeErrorClosure invalidAccountData) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let public1 ←
      AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public val
    first_decoded tx1 error public1 public_bytes proof k
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec U8) (core.convert.FromSame E) residual

/-- Exact symbolic equality to the retained body through an observer-off
continuation. It includes failure and divergence, not just successful runs. -/
theorem first_eq_historical {E F : Type} (invalidAccountData : E)
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E) (public_bytes proof : Slice U8) (k : Usize) :
    first invalidAccountData tx1 error public_bytes proof k =
      AspisR1PublicPreparation.FirstCaller.first invalidAccountData
        (fun p b q n h _ => tx1 p b q n h none) (fun _ => ok ()) error
        public_bytes proof k := by
  simp only [first, first_decoded, observer, bind_tc_ok,
    AspisR1PublicPreparation.FirstCaller.first] <;> rfl

/-- The historical success theorem re-pinned to the unobserved continuation. -/
theorem first_success {E F : Type} (invalidAccountData : E)
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E) (asf8 proof : Slice U8) (k : Usize)
    (out : alloc.vec.Vec U8)
    (h : first invalidAccountData tx1 error asf8 proof k = ok (.Ok out)) :
    ∃ (s : DecoderStatement) (supplied : Public),
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
        asf8 = ok (.Ok s) ∧
      supplied = preparationPublic s ∧
      tx1 supplied asf8 proof k () none = ok (.Ok out) := by
  rw [first_eq_historical] at h
  exact AspisR1PublicPreparation.FirstCaller.first_success invalidAccountData
    (fun p b q n d _ => tx1 p b q n d none) (fun _ => ok ()) error
    asf8 proof k out h

#print axioms observer
#print axioms first_decoded
#print axioms first
#print axioms first_eq_historical
#print axioms first_success
end AspisR1S2ObserverOff
