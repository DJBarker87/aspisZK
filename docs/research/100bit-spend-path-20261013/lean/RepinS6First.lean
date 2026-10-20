import ExtractedFirstCallerReachability

/-! Complete emitted frozen first/first_decoded control flow, interpreted with
the checked decoder and selector of PreparationBinding and explicit downstream
functions. No SDK/runtime or downstream tx1 refinement is asserted here.
The frozen release observer is None; original byte slices are retained. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.RepinS6First
open PreparationBinding FirstCaller

/-- The emitted observer body for the release feature set. -/
def observer : Result (Option (Phase → Result Unit)) := do
  ok none

def first_decoded {E F : Type}
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E)
    (public1 : Public) (public_bytes proof : Slice U8) (k : Usize) :
    Result (core.result.Result (alloc.vec.Vec U8) E) := do
  let o ← observer
  let r ← tx1 public1 public_bytes proof k () o
  core.result.Result.map_err (BuiltinFnOnce F E) r error

def first {E F : Type} (invalidAccountData : E)
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E)
    (public_bytes proof : Slice U8) (k : Usize) :
    Result (core.result.Result (alloc.vec.Vec U8) E) := do
  let r ← decode public_bytes
  let r1 ← core.result.Result.map_err (decodeErrorClosure invalidAccountData) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let p ← pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public val
    first_decoded tx1 error p public_bytes proof k
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec U8) (core.convert.FromSame E) residual

/-- Full-result equality, including failure, divergence and mapped errors.
The historical observer argument is discarded by the explicit continuation;
the actual downstream call receives the frozen release observer None. -/
theorem first_eq_historical {E F : Type} (invalidAccountData : E)
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E) (bytes proof : Slice U8) (k : Usize) :
    first invalidAccountData tx1 error bytes proof k =
      FirstCaller.first invalidAccountData
        (fun p b pr n digest _ => tx1 p b pr n digest none)
        (fun _ => ok ()) error bytes proof k := by
  rfl

/-- No decoder or chosen-public hypothesis is required: caller success
produces the decoder witness and the exact public supplied to tx1. -/
theorem first_success {E F : Type} (invalidAccountData : E)
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E) (bytes proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : first invalidAccountData tx1 error bytes proof k = ok (.Ok out)) :
    ∃ (s : DecoderStatement) (supplied : Public),
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
        bytes = ok (.Ok s) ∧ supplied = preparationPublic s ∧
      tx1 supplied bytes proof k () none = ok (.Ok out) := by
  rw [first_eq_historical] at h
  exact FirstCaller.first_success invalidAccountData
    (fun p b pr n digest _ => tx1 p b pr n digest none)
    (fun _ => ok ()) error bytes proof k out h

/-- The adapter can reuse an already decoded statement without changing
public bytes, proof bytes, k or the result/error boundary. Its separate
same-byte decoder binding must be supplied by the adapter execution proof. -/
theorem reuse_decoded {E F : Type} (invalidAccountData : E)
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E) (bytes proof : Slice U8) (k : Usize) (s : DecoderStatement)
    (hd : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
      bytes = ok (.Ok s)) :
    first invalidAccountData tx1 error bytes proof k =
      first_decoded tx1 error (preparationPublic s) bytes proof k := by
  unfold first decode
  rw [hd]
  simp only [bind_tc_ok, core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch, actual_selector_eq]

#print axioms observer
#print axioms first_decoded
#print axioms first
#print axioms first_eq_historical
#print axioms first_success
#print axioms reuse_decoded
end AspisR1PublicPreparation.RepinS6First
