import ExtractedPublicPreparationBinding

/-! Parametric downstream interpretation of the complete emitted `first` body.
The decoder is the checked actual decoder and the selector the checked actual
selector on its fixed carrier. The three downstream globals are explicit
parameters. Their effects, failure/divergence, observer argument and error map
are retained. No downstream tx1, SDK, runtime, or custody theorem is claimed. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicPreparation.FirstCaller
open PreparationBinding
abbrev Statement := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Public := pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev DecoderStatement := AspisR1TerminalDecoder.PublicBinding.Statement
abbrev DecodeError := AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

inductive Phase where
  | Parsed | Semantic | SemanticPart (i : U8) | Prepare | CheckpointRead
  | Merkle (i : Usize) | Query (i : Usize) | QueryPart (i : Usize) (j : U8)
  | CheckpointWrite | Relation | Final

/-- Interpret the emitted decoder boundary with the already checked actual
computation, transporting only its returned source carrier. -/
def decode (bytes : Slice U8) : Result (core.result.Result Statement DecodeError) := do
  let r ← AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes
  match r with
  | .Ok s => ok (.Ok (fromStatement s))
  | .Err e => ok (.Err e)

/-- The generated closure ignores the decoder error and returns this value. -/
def decodeErrorClosure {E : Type} (invalidAccountData : E) :
    core.ops.function.FnOnce Unit DecodeError E :=
  { call_once := fun _ _ => ok invalidAccountData }

/-- Full emitted caller control flow. `()` is the emitted unit-struct
SolanaDigest carrier; the downstream interpreter receives it unchanged. -/
def first {E F : Type} (invalidAccountData : E)
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (mark : Phase → Result Unit) (error : F → Result E)
    (public_bytes : Slice U8) (proof : Slice U8) (k : Usize) :
    Result (core.result.Result (alloc.vec.Vec U8) E) := do
  let r ← decode public_bytes
  let r1 ← core.result.Result.map_err (decodeErrorClosure invalidAccountData) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let public1 ←
      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public val
    let r2 ← tx1 public1 public_bytes proof k () (some mark)
    core.result.Result.map_err (BuiltinFnOnce F E) r2 error
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec U8) (core.convert.FromSame E) residual

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem map_error_success {E F A : Type} (r : core.result.Result A F)
    (error : F → Result E) (out : A)
    (h : core.result.Result.map_err (BuiltinFnOnce F E) r error = ok (.Ok out)) :
    r = .Ok out := by
  cases r with
  | Ok a =>
    change ok (core.result.Result.Ok a) = ok (.Ok out) at h
    have ha : a = out := core.result.Result.Ok.inj (Result.ok.inj h)
    subst out
    rfl
  | Err e =>
    change (do let mapped ← error e; ok (core.result.Result.Err mapped)) = ok (.Ok out) at h
    obtain ⟨mapped, _, h⟩ := bind_success (error e) _ _ h
    cases h

/-- Caller success supplies hd and the exact public passed to the downstream
call. There is no hd, chosen-public equality, or continuation-success premise. -/
theorem first_success {E F : Type} (invalidAccountData : E)
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (mark : Phase → Result Unit) (error : F → Result E)
    (asf8 proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : first invalidAccountData tx1 mark error asf8 proof k = ok (.Ok out)) :
    ∃ (s : DecoderStatement) (supplied : Public),
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
        asf8 = ok (.Ok s) ∧
      supplied = preparationPublic s ∧
      tx1 supplied asf8 proof k () (some mark) = ok (.Ok out) := by
  unfold first at h
  obtain ⟨r, hr, h⟩ := bind_success (decode asf8) _ _ h
  cases r with
  | Err e =>
    simp only [bind_tc_ok, core.result.Result.map_err, decodeErrorClosure,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok selected =>
    unfold decode at hr
    obtain ⟨decoded, hd, hselected⟩ := bind_success
      (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 asf8) _ _ hr
    cases decoded with
    | Err e => cases hselected
    | Ok s =>
      have hs : fromStatement s = selected :=
        core.result.Result.Ok.inj (Result.ok.inj hselected)
      rw [← hs] at h
      simp only [bind_tc_ok, core.result.Result.map_err,
        core.result.Result.Insts.CoreOpsTry.branch, actual_selector_eq] at h
      obtain ⟨r, hcall, hmap⟩ := bind_success
        (tx1 (preparationPublic s) asf8 proof k () (some mark)) _ _ h
      have hr := map_error_success r error out hmap
      exact ⟨s, preparationPublic s, hd, rfl, hr ▸ hcall⟩

#print axioms decode
#print axioms first
#print axioms first_success
end AspisR1PublicPreparation.FirstCaller
