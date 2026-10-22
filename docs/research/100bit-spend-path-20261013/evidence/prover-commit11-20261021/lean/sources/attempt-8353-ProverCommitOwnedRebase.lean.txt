import R1Z.ProverCommitOwnedWindow
set_option autoImplicit false
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R0Z.FsStatement
open R1Z.ProverCommitStepLoop (State Hash)
open R1Z.ProverCommitStreamSource (Bytes32 blockSlices)

/-- The local table is a restriction of the retained global answers. Values
past the allocation are never queried by the bounded scalar theorem below. -/
def windowAnswers {n : Nat} (answers : Fin n → OracleAnswer) (base : Nat) :
    Fin 9 → OracleAnswer := fun i =>
  if h : base+i.val < n then answers ⟨base+i.val,h⟩ else fun _ => 0

def windowHash {n : Nat} (answers : Fin n → OracleAnswer) (base : Nat) : Hash := fun frame =>
  let counter := littleEndian (match frame.val[2]? with | none => [] | some bytes => bytes.val)
  if h : base ≤ counter ∧ counter-base < 9 then
    ok (answerBytes (windowAnswers answers base ⟨counter-base,h.2⟩))
  else fail .panic

theorem windowHash_at {n : Nat} (answers : Fin n → OracleAnswer) (base : Nat)
    (domain : Slice U8) (seed : Bytes32) (counter : U64)
    (lower : base ≤ counter.val) (upper : counter.val-base < 9) (bound : counter.val < n) :
    windowHash answers base (blockSlices domain seed counter) =
      blockHash answers (blockSlices domain seed counter) := by
  rw [blockHash_at answers domain seed counter bound]
  simp only [windowHash, blockSlices, Aeneas.Std.Array.to_slice, Aeneas.Std.Array.make,
    List.getElem?_cons_zero, List.getElem?_cons_succ, littleEndian_counter,
    dif_pos (show base ≤ counter.val ∧ counter.val-base < 9 from ⟨lower,upper⟩)]
  have index : base+(counter.val-base) = counter.val := by omega
  simp only [windowAnswers, index, dif_pos bound]

/-- The Rust local-ROM wrapping subtraction is ordinary subtraction throughout
these global windows: there is neither counter wrap nor index wrap. -/
theorem window_wrapping_offset (counter base : Nat) (bound : counter < 2^64)
    (lower : base ≤ counter) :
    (counter+2^64-base)%2^64 = counter-base := by
  have eq : counter+2^64-base = counter-base+2^64 := by omega
  rw [eq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Universal rebasing of one full scalar computation to the exact nine-answer
backend used by the local certificates. Repeated windows share their global
answers by construction; no whole array is certified with a nine-block ROM. -/
theorem scalar_rebase {n : Nat} (answers : Fin n → OracleAnswer)
    (domain : Slice U8) (capacity : n < 2^64) (state : State)
    (before : valid n state) (room : position state+16 ≤ n*8) :
    prover_commit_reference.limb_caller (blockHash answers) domain state =
      prover_commit_reference.limb_caller (windowHash answers (position state/8)) domain state := by
  apply scalar_window answers _ domain capacity state before room
  intro seed counter lower upper
  have window := scalar_block_window (position state) counter.val lower upper
  apply (windowHash_at answers (position state/8) domain seed counter window.1
    (by omega) (by omega)).symm

/-- A valid global cursor starts at offset zero or one in its rebased table,
inside the scalar contract's six-block starting margin. -/
theorem scalar_window_offset {n : Nat} (state : State) (before : valid n state) :
    position state/8 ≤ state.counter.val ∧ state.counter.val-position state/8 ≤ 1 := by
  unfold valid position at *
  omega

#print axioms windowHash_at
#print axioms window_wrapping_offset
#print axioms scalar_rebase
#print axioms scalar_window_offset
end R1Z.ProverCommitOwnedDecoder
