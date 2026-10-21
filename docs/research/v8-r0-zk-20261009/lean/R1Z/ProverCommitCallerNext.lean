import AspisR1ProverCaller7.Funs
import R1Z.ProverCommitExtractedLoop

/-! The new owned lowering uses the same Rust State and next-word body as
the earlier reference. This explicit carrier transport preserves fail/div. -/
set_option autoImplicit false
namespace R1Z.ProverCommitCallerNext
open Aeneas Aeneas.Std Result ControlFlow
abbrev State := AspisR1ProverCaller7.prover_commit_reference.State
abbrev OldState := AspisR1ProverCommitReference.prover_commit_reference.State
abbrev Hash := Slice (Slice U8) → Result (Aeneas.Std.Array U8 32#usize)

def toOldState (s : State) : OldState := ⟨s.seed,s.counter,s.block,s.word⟩
def fromOldState (s : OldState) : State := ⟨s.seed,s.counter,s.block,s.word⟩

theorem state_roundtrip (s : State) : fromOldState (toOldState s) = s := by
  cases s
  rfl

theorem old_state_roundtrip (s : OldState) : toOldState (fromOldState s) = s := by
  cases s
  rfl

theorem next_bridge (hash : Hash) (domain : Slice U8) (state : State) :
    (do
      let (word,after) ← AspisR1ProverCaller7.prover_commit_reference.next hash domain state
      ok (word,toOldState after)) =
      AspisR1ProverCommitReference.prover_commit_reference.next hash domain (toOldState state) := by
  simp only [AspisR1ProverCaller7.prover_commit_reference.next,
    AspisR1ProverCommitReference.prover_commit_reference.next, toOldState,
    bind_assoc_eq, bind_tc_ok]
  congr 1
  funext triple
  rcases triple with ⟨counter, block, word⟩
  simp only [Aeneas.Std.uncurry_apply_pair, bind_assoc_eq, bind_tc_ok, toOldState]

#print axioms state_roundtrip
#print axioms old_state_roundtrip
#print axioms next_bridge
end R1Z.ProverCommitCallerNext
