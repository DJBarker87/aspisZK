import R1Z.ProverCommitOwnedBackend
set_option autoImplicit false
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R0Z.FsStatement
open R1Z.ProverCommitStepLoop (State Hash)
open R1Z.ProverCommitStreamSource (Bytes32 blockSlices)

theorem bind_success {A B : Type} (run : Result A) (f : A → Result B)
    (value : B) (success : (do let a ← run; f a) = ok value) :
    ∃ a, run = ok a ∧ f a = ok value := by
  cases run with
  | fail e => cases success
  | div => cases success
  | ok a => exact ⟨a, rfl, success⟩

def readBlock (block : Bytes32) (word : Usize) : Result U32 := do
  let offset := Usize.wrapping_mul word 4#usize
  let b₀ ← Aeneas.Std.Array.index_usize block offset
  let b₁ ← Aeneas.Std.Array.index_usize block (Usize.wrapping_add offset 1#usize)
  let b₂ ← Aeneas.Std.Array.index_usize block (Usize.wrapping_add offset 2#usize)
  let b₃ ← Aeneas.Std.Array.index_usize block (Usize.wrapping_add offset 3#usize)
  ok (core.num.U32.from_le_bytes (Aeneas.Std.Array.make 4#usize [b₀,b₁,b₂,b₃]))

def refill (hash : Hash) (domain : Slice U8) (state : State) :
    Result (U64 × Bytes32 × Usize) :=
  if state.word = 8#usize then do
    let block ← hash (blockSlices domain state.seed state.counter)
    ok (core.num.U64.wrapping_add state.counter 1#u64, block, 0#usize)
  else ok (state.counter, state.block, state.word)

theorem next_factor (hash : Hash) (domain : Slice U8) (state : State) :
    prover_commit_reference.next hash domain state = (do
      let (counter, block, word) ← refill hash domain state
      let value ← readBlock block word
      ok (value, {state with counter := counter, block := block, word := Usize.wrapping_add word 1#usize})) := by
  simp only [prover_commit_reference.next, refill, readBlock, blockSlices,
    lift, bind_assoc_eq, bind_tc_ok]

/-- A source cursor invariant, including the empty initial cache. -/
def valid (blocks : Nat) (state : State) : Prop :=
  state.counter.val ≤ blocks ∧ state.word.val ≤ 8 ∧
    (state.counter.val = 0 → state.word.val = 8)

def position (state : State) : Nat := 8*state.counter.val + state.word.val - 8

theorem position_bound {blocks : Nat} {state : State} (h : valid blocks state) :
    position state ≤ 8*blocks := by unfold valid position at *; omega

theorem small_increment (word : Usize) (bound : word.val ≤ 8) :
    (Usize.wrapping_add word 1#usize).val = word.val + 1 := by
  rw [Usize.wrapping_add_val_eq]
  have small : 2^32 ≤ UScalar.size .Usize := by
    rw [UScalar.size_def]
    exact Nat.pow_le_pow_right (by decide) System.Platform.le_numBits
  have one : (1#usize).val = 1 := by scalar_tac
  rw [one, Nat.mod_eq_of_lt (by omega)]

#print axioms bind_success
#print axioms next_factor
#print axioms position_bound
#print axioms small_increment
end R1Z.ProverCommitOwnedDecoder
