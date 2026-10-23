import S2E_Model
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2E
open S2E_Reference.S2E_Reference
abbrev SDK := S2E_Reference.S2E_Reference.OwnedSdk
abbrev Statement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev PE := solana_program_error.ProgramError
abbrev CallerResult (S : Type) := (core.result.Result Unit PE) × S × SDK

/-- Inversion of the actual extracted Result carrier, not an assumed cut view. -/
theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a) = ok out) : ∃ a, m = ok a ∧ f a = ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Decoding and statement cleanup belong to this single reference continuation.
No native correspondence or concrete child implementation is assumed here. -/
theorem decoded_success {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (state finalState : S) (sdk finalSdk : SDK)
    (publicInput data : Slice U8)
    (accepted : decoded_continuation ops children state sdk publicInput data =
      ok (.Ok (),finalState,finalSdk)) :
    ∃ statement state1 state2,
      children.decode state publicInput = ok (.Ok statement,state1) ∧
      statement_continuation ops children state1 sdk statement publicInput data =
        ok (.Ok (),state2,finalSdk) ∧
      children.drop_statement state2 statement = ok finalState := by
  unfold decoded_continuation at accepted
  obtain ⟨⟨reply,state1⟩,decoded,rest⟩ := bind_success _ _ _ accepted
  cases reply with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame] at rest
    cases rest
  | Ok statement =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
    obtain ⟨⟨result,state2,sdk2⟩,continued,rest⟩ := bind_success _ _ _ rest
    obtain ⟨state3,dropped,rest⟩ := bind_success _ _ _ rest
    cases rest
    exact ⟨statement,state1,state2,decoded,continued,dropped⟩

/-- Successful copy uses this returned checkpoint and this exact length guard;
the drop receives the state after that same copy. -/
theorem after_first_success {C S : Type} (children : Children C S)
    (state finalState : S) (sdk finalSdk : SDK) (slot : Usize)
    (checkpoint : alloc.vec.Vec U8)
    (accepted : after_first children state sdk slot checkpoint =
      ok (.Ok (),finalState,finalSdk)) :
    ∃ cell state1,
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
        sdk.data_cells slot = ok cell ∧
      alloc.vec.Vec.len checkpoint = alloc.vec.Vec.len cell.bytes ∧
      children.copy state sdk slot (alloc.vec.Vec.deref checkpoint) = ok (state1,finalSdk) ∧
      children.drop_checkpoint state1 checkpoint = ok finalState := by
  unfold after_first at accepted
  obtain ⟨cell,read,rest⟩ := bind_success _ _ _ accepted
  by_cases lengths : alloc.vec.Vec.len checkpoint = alloc.vec.Vec.len cell.bytes
  · simp only [bne_iff_ne, ne_eq, lengths, not_true_eq_false, if_false] at rest
    obtain ⟨⟨state1,sdk1⟩,copied,rest⟩ := bind_success _ _ _ rest
    simp only [bind_tc_ok] at rest
    obtain ⟨state2,dropped,rest⟩ := bind_success _ _ _ rest
    cases rest
    exact ⟨cell,state1,read,lengths,copied,dropped⟩
  · simp only [bne_iff_ne, ne_eq, lengths, not_false_eq_true, if_true, bind_tc_ok] at rest
    obtain ⟨state1,dropped,rest⟩ := bind_success _ _ _ rest
    cases rest

#print axioms bind_success
#print axioms decoded_success
#print axioms after_first_success
end AspisR1.S2E
