import AspisR1ProverCommitReference.Funs

/-! Focused facts about the owned sampler lowering. The callbacks are arbitrary;
these statements do not identify a complete source tape or its fibres. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.ProverCommitReferenceSource
open AspisR1ProverCommitReference
abbrev State := prover_commit_reference.State
abbrev Hash := Slice (Slice U8) → Result (Aeneas.Std.Array U8 32#usize)
abbrev Sample := core.result.Result aspis_core.field.M31
  state_only_hiding.StateOnlyMaskBuildError

theorem next_cached (hash₁ hash₂ : Hash) (domain : Slice U8) (state : State)
    (cached : state.word ≠ 8#usize) :
    prover_commit_reference.next hash₁ domain state =
      prover_commit_reference.next hash₂ domain state := by
  simp only [prover_commit_reference.next, if_neg cached]

theorem terminal (hash : Hash) (domain : Slice U8) (state : State) (result : Sample) :
    prover_commit_reference.limb_loop.body hash domain state 16#i32 result =
      ok (done (result, state)) := by
  simp [prover_commit_reference.limb_loop.body]

theorem success_step (hash : Hash) (domain : Slice U8) (state : State)
    (attempts : I32) (value : U32) (running : attempts < 16#i32) :
    prover_commit_reference.limb_loop.body hash domain state attempts (.Ok value) =
      ok (cont (state, I32.wrapping_add attempts 1#i32, .Ok value)) := by
  simp [prover_commit_reference.limb_loop.body, running, lift]

#print axioms next_cached
#print axioms terminal
#print axioms success_step
end R1Z.ProverCommitReferenceSource
