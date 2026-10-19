import CuSavingsPublicDecodeSource

/-! Consume the reuse proof at the existing caller's acceptance boundary.
No decoder-success or public-value-equality premise is added. The original
actual decoder and selector supply the same semantic public and byte buffer
for every successful entry. This is candidate 6, with other changes held fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsPublicDecodeTransfer
open Aeneas Aeneas.Std Result
open CuSavingsPublicDecode CuSavingsPublicDecodeSource

def entry {S P D E F O Obs : Type} (B : Boundaries S P D E F O Obs)
    (invalid : E) (bytes proof : Slice U8) (k : Usize) (obs : Obs) :
    Result (core.result.Result O E) := do
  let result ← decodeBox B invalid bytes
  match result with
  | .Err err => .ok (.Err err)
  | .Ok statement => do
    let pub ← B.select statement
    sourceDecoded B pub bytes proof k obs

theorem entry_eq_source_first {S P D E F O Obs : Type}
    (B : Boundaries S P D E F O Obs) (invalid : E)
    (bytes proof : Slice U8) (k : Usize) (obs : Obs) :
    entry B invalid bytes proof k obs = sourceFirst B invalid bytes proof k obs := by
  rw [source_first_eq]
  unfold entry decodeBox first
  cases hd : B.decode bytes with
  | fail e => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err err => rfl
    | Ok statement =>
      simp only [bind_tc_ok,source_decoded_eq]

abbrev ActualPublic := AspisR1PublicPreparation.FirstCaller.Public
abbrev ActualStatement := AspisR1PublicPreparation.FirstCaller.Statement
abbrev Phase := AspisR1PublicPreparation.FirstCaller.Phase
abbrev Observer := Option (Phase → Result Unit)
abbrev Tx1 (F : Type) := ActualPublic → Slice U8 → Slice U8 → Usize → Unit →
  Observer → Result (core.result.Result (alloc.vec.Vec U8) F)

theorem entry_eq_original_first {E F : Type} (invalid : E) (tx1 : Tx1 F)
    (mark : Phase → Result Unit) (error : F → Result E)
    (bytes proof : Slice U8) (k : Usize) :
    entry (actualBoundaries tx1 error) invalid bytes proof k (some mark) =
      AspisR1PublicPreparation.FirstCaller.first invalid tx1 mark error bytes proof k := by
  exact (entry_eq_source_first (actualBoundaries tx1 error) invalid bytes proof k (some mark)).trans
    (original_first_eq invalid tx1 mark error bytes proof k).symm

/-- Reused entry acceptance produces the same actual raw decode and supplied
semantic public as the reference caller. This consumes the old first_success
proof, rather than assuming the decoder/caller correspondence anew. -/
theorem entry_success {E F : Type} (invalid : E) (tx1 : Tx1 F)
    (mark : Phase → Result Unit) (error : F → Result E)
    (bytes proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : entry (actualBoundaries tx1 error) invalid bytes proof k (some mark) = .ok (.Ok out)) :
    ∃ (statement : AspisR1PublicPreparation.FirstCaller.DecoderStatement)
      (supplied : ActualPublic),
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
        bytes = .ok (.Ok statement) ∧
      supplied = AspisR1PublicPreparation.PreparationBinding.preparationPublic statement ∧
      tx1 supplied bytes proof k () (some mark) = .ok (.Ok out) := by
  rw [entry_eq_original_first] at h
  exact AspisR1PublicPreparation.FirstCaller.first_success invalid tx1 mark error bytes proof k out h

#print axioms entry
#print axioms entry_eq_source_first
#print axioms entry_eq_original_first
#print axioms entry_success
end AspisR1.CuSavingsPublicDecodeTransfer
