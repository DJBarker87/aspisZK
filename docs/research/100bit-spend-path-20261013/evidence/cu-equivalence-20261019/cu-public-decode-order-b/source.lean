import CuSavingsPublicDecodeClosed

/-! The new semantic-public argument is evaluated at the call site. Prove its
actual selector is total on the earlier decoded statement, so moving it past
other argument construction preserves every failure/divergence path. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsPublicDecodeOrder
open Aeneas Aeneas.Std Result
open CuSavingsPublicDecode CuSavingsPublicDecodeSource CuSavingsPublicDecodeClosed
open CuSavingsPublicDecodeTransfer

abbrev selectActual (statement : ActualStatement) :=
  AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
    (alloc.boxed.Box.deref statement)

theorem actual_boxed_eq {E F : Type} (invalid : E) (tx1 : Tx1 F) (error : F → Result E)
    (bytes : Slice U8) :
    boxedSource (actualBoundaries tx1 error) invalid bytes =
      (do
        let r ← AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes
        match r with
        | .Ok statement => .ok (.Ok (AspisR1PublicPreparation.PreparationBinding.fromStatement statement))
        | .Err _ => .ok (.Err invalid)) := by
  rw [boxed_eq]
  unfold decodeBox actualBoundaries AspisR1PublicPreparation.FirstCaller.decode
  dsimp only
  cases AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes with
  | fail e => rfl
  | div => rfl
  | ok r => cases r <;> rfl

theorem select_after_box {E F : Type} (invalid : E) (tx1 : Tx1 F) (error : F → Result E)
    (bytes : Slice U8) (statement : ActualStatement)
    (h : boxedSource (actualBoundaries tx1 error) invalid bytes = .ok (.Ok statement)) :
    ∃ pub, selectActual statement = .ok pub := by
  rw [actual_boxed_eq] at h
  cases hd : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes with
  | fail e => simp only [hd,bind_tc_fail] at h;cases h
  | div => simp only [hd,bind_tc_div] at h;cases h
  | ok r =>
    cases r with
    | Err e => simp only [hd,bind_tc_ok] at h;cases h
    | Ok raw =>
      simp only [hd,bind_tc_ok] at h
      have hs := core.result.Result.Ok.inj (Result.ok.inj h)
      rw [←hs]
      exact ⟨AspisR1PublicPreparation.PreparationBinding.preparationPublic raw,
        AspisR1PublicPreparation.PreparationBinding.actual_selector_eq raw⟩

theorem argument_order_eq {E F Arg A : Type}
    (invalid : E) (tx1 : Tx1 F) (error : F → Result E) (bytes : Slice U8)
    (reject : E → Result A) (arguments : Result Arg)
    (call : ActualPublic → Arg → Result A) :
    (do
      let r ← boxedSource (actualBoundaries tx1 error) invalid bytes
      match r with
      | .Err e => reject e
      | .Ok statement => do
        let args ← arguments
        let pub ← selectActual statement
        call pub args) =
    (do
      let r ← boxedSource (actualBoundaries tx1 error) invalid bytes
      match r with
      | .Err e => reject e
      | .Ok statement => do
        let pub ← selectActual statement
        let args ← arguments
        call pub args) := by
  cases hb : boxedSource (actualBoundaries tx1 error) invalid bytes with
  | fail e => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err e => rfl
    | Ok statement =>
      obtain ⟨pub,hpub⟩ := select_after_box invalid tx1 error bytes statement hb
      simp only [bind_tc_ok,hpub]

#print axioms actual_boxed_eq
#print axioms select_after_box
#print axioms argument_order_eq
end AspisR1.CuSavingsPublicDecodeOrder
