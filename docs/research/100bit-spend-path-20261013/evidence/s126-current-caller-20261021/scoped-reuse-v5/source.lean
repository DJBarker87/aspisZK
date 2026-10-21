import RepinS6First

/-! Contextual reuse under the checked *actual* decoder. This removes the
independent decoder-success hypothesis from the context equality. The arbitrary
continuation retains validators, proof guards, error paths and writes; it is
not asserted to be a translated AccountInfo stage1. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.S6DecoderScopedReuseV1
open PreparationBinding FirstCaller
open RepinS6First

abbrev decodeActual :=
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1

/-- No success or totality assumption: the statement comes from this very
same decoder on bytes, and both sides retain exactly the same continuation.
Failure, divergence, ordinary decoder rejection and downstream errors agree. -/
theorem decoder_scoped_reuse {E F A : Type} (invalidAccountData : E)
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E) (bytes proof : Slice U8) (k : Usize)
    (reject : DecodeError → Result A)
    (tail : DecoderStatement → Result (core.result.Result (alloc.vec.Vec U8) E) → Result A) :
    (do
      let r ← decodeActual bytes
      match r with
      | .Err e => reject e
      | .Ok s => tail s (RepinS6First.first invalidAccountData tx1 error bytes proof k)) =
    (do
      let r ← decodeActual bytes
      match r with
      | .Err e => reject e
      | .Ok s => tail s (first_decoded tx1 error (preparationPublic s) bytes proof k)) := by
  cases hd : decodeActual bytes with
  | fail e => rfl
  | div => rfl
  | ok r =>
    cases r with
    | Err e => rfl
    | Ok s =>
      simp only [bind_tc_ok]
      rw [reuse_decoded invalidAccountData tx1 error bytes proof k s hd]

/-- Success of first_decoded already forces the *actual* child to return the
same checkpoint with None. Error mapping cannot turn Rust Err into Rust Ok. -/
theorem first_decoded_success {E F : Type}
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E) (pub : Public) (bytes proof : Slice U8)
    (k : Usize) (out : alloc.vec.Vec U8)
    (h : first_decoded tx1 error pub bytes proof k = ok (.Ok out)) :
    tx1 pub bytes proof k () none = ok (.Ok out) := by
  unfold first_decoded observer at h
  simp only [bind_tc_ok] at h
  cases ht : tx1 pub bytes proof k () none with
  | fail e => simp only [ht, bind_tc_fail] at h; cases h
  | div => simp only [ht, bind_tc_div] at h; cases h
  | ok r =>
    rw [ht] at h
    simp only [bind_tc_ok] at h
    cases r with
    | Ok v =>
      simp only [core.result.Result.map_err] at h
      cases h
      rfl
    | Err e =>
      simp only [core.result.Result.map_err] at h
      cases he : error e with
      | fail e' => simp only [he, bind_tc_fail] at h; cases h
      | div => simp only [he, bind_tc_div] at h; cases h
      | ok e' => simp only [he, bind_tc_ok] at h; cases h

/-- A concrete decode-then-call scope derives its own decoder equation,
semantic selection, exact bytes/proof/k and observer-off child success. -/
theorem decoded_scope_success {E F : Type} (invalidAccountData : E)
    (tx1 : Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E) (bytes proof : Slice U8) (k : Usize)
    (out : alloc.vec.Vec U8)
    (h : (do
      let r ← decodeActual bytes
      match r with
      | .Err _ => ok (core.result.Result.Err invalidAccountData)
      | .Ok s => first_decoded tx1 error (preparationPublic s) bytes proof k)
      = ok (.Ok out)) :
    ∃ s : DecoderStatement,
      decodeActual bytes = ok (.Ok s) ∧
      RepinS6First.first invalidAccountData tx1 error bytes proof k =
        first_decoded tx1 error (preparationPublic s) bytes proof k ∧
      tx1 (preparationPublic s) bytes proof k () none = ok (.Ok out) := by
  cases hd : decodeActual bytes with
  | fail e => simp only [hd, bind_tc_fail] at h; cases h
  | div => simp only [hd, bind_tc_div] at h; cases h
  | ok r =>
    rw [hd] at h
    simp only [bind_tc_ok] at h
    cases r with
    | Err e => cases h
    | Ok s => exact ⟨s,rfl,reuse_decoded invalidAccountData tx1 error bytes proof k s hd,
        first_decoded_success tx1 error (preparationPublic s) bytes proof k out h⟩

#print axioms decoder_scoped_reuse
#print axioms first_decoded_success
#print axioms decoded_scope_success
end AspisR1PublicPreparation.S6DecoderScopedReuseV1
