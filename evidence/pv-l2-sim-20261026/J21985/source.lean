import R1Z.PV_L2_F3FullSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3SeedFrames
open Aeneas Aeneas.Std Result AspisR1ProverStep8 R0Z.FsStatement
open R1Z.ProverCommitStepLoop (State Hash)
open R1Z.ProverCommitOwnedDecoder R1Z.ProverCommitStreamSource

def reseed (seed : Bytes32) (state : State) : State := {state with seed := seed}

def mapAfter (seed : Bytes32) : Result (U32 × State) → Result (U32 × State)
  | .fail e => .fail e
  | .div => .div
  | .ok (word,state) => .ok (word,reseed seed state)

/-- The finite counter backend deliberately ignores the domain and seed
frame. This fact does NOT identify it with the actual adaptive ROM. -/
theorem blockHash_seed {n : Nat} (answers : Fin n → OracleAnswer)
    (domain : Slice U8) (seed seed' : Bytes32) (counter : U64) :
    blockHash answers (blockSlices domain seed counter) =
      blockHash answers (blockSlices domain seed' counter) := rfl

/-- Actual extracted next operation with an arbitrary retained E1 seed;
same word/counter/cache/error, seed restored in the returned state. -/
theorem next_reseed {n : Nat} (answers : Fin n → OracleAnswer) (domain : Slice U8)
    (seed : Bytes32) (state : State) :
    prover_commit_reference.next (blockHash answers) domain (reseed seed state) =
      mapAfter seed (prover_commit_reference.next (blockHash answers) domain state) := by
  rw [next_factor,next_factor]
  by_cases h : state.word=8#usize
  · simp only [refill,reseed,h,if_true]
    rw [blockHash_seed answers domain seed state.seed state.counter]
    cases hb : blockHash answers (blockSlices domain state.seed state.counter) <;>
      simp only [hb,bind_tc_fail,bind_tc_div,bind_tc_ok,mapAfter]
    rename_i block
    dsimp only
    cases readBlock block 0#usize <;> rfl
  · simp only [refill,reseed,h,if_false,bind_tc_ok]
    dsimp only
    cases readBlock state.block state.word <;> rfl

def read (seed : Bytes32) (r : PV_L2_F3Recorded.Read) : PV_L2_F3Recorded.Read :=
  ⟨reseed seed r.before,mapAfter seed r.answer⟩

theorem actual_answer {n : Nat} (answers : Fin n → OracleAnswer) (domain : Slice U8)
    (seed : Bytes32) (r : PV_L2_F3Recorded.Read)
    (actual : r.answer=prover_commit_reference.next (blockHash answers) domain r.before) :
    (read seed r).answer =
      prover_commit_reference.next (blockHash answers) domain (read seed r).before := by
  exact (congrArg (mapAfter seed) actual).trans (next_reseed answers domain seed r.before).symm

theorem refill_frame (domain : Slice U8) (seed : Bytes32) (r : PV_L2_F3Recorded.Read) :
    PV_L2_F3Recorded.refill domain (read seed r) =
      if r.before.word=8#usize then some (blockSlices domain seed r.before.counter) else none := rfl

#print axioms blockHash_seed
#print axioms next_reseed
#print axioms actual_answer
#print axioms refill_frame
end R1Z.PV_L2_F3SeedFrames
