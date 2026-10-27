import R1Z.PV_RunJoin_ParentNoopRounds

/-! Complete threaded outputs of the shipped no-op callback folds. Round/input
bookkeeping remains explicit; only their unused final values are existential. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ParentRoundTotal
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort PV_Src_PortSboxStep
open PV_RunJoin_SourceRoundFold PV_RunJoin_ParentNoopRounds

theorem full_total_threaded (kind : Usize → poseidon2.Poseidon2RoundKind)
    (xs : List (Usize × State)) (s input : State) (round : U8) (hs : Canonical s) :
    ∃ out nextRound nextInput,
      fullSteps callback kind xs s () round input = ok (out,(),nextRound,nextInput) ∧
      full xs s = ok out ∧ Canonical out := by
  induction xs generalizing s input round with
  | nil => exact ⟨s,round,input,rfl,rfl,hs⟩
  | cons head tail ih =>
    rcases head with ⟨index,c⟩
    obtain ⟨out,ho,hcan⟩ := PV_RunJoin_SourceRoundFold.full_total s c
    obtain ⟨last,r,i,hl,hp,hc⟩ := ih out out (U8.wrapping_add round 1#u8) hcan
    refine ⟨last,r,i,?_,?_,hc⟩
    · simp only [fullSteps,ho,bind_tc_ok,poseidon2.merkle_node_compress_v3.closure.Insts.CoreOpsFunctionFnMutTuplePoseidon2RoundTransitionTuple.call_mut,hl]
      rfl
    · simp only [full,ho,bind_tc_ok,hp]

theorem internal_total_threaded (xs : List (Usize × U32))
    (s input : State) (round : U8) (hs : Canonical s) :
    ∃ out nextRound nextInput,
      PV_RunJoin_SourceInternalRounds.steps callback xs s () round input =
        ok (out,(),nextRound,nextInput) ∧
      internal xs s = ok out ∧ Canonical out := by
  induction xs generalizing s input round with
  | nil => exact ⟨s,round,input,rfl,rfl,hs⟩
  | cons head tail ih =>
    rcases head with ⟨index,c⟩
    obtain ⟨out,ho,hcan⟩ := PV_RunJoin_SourceInternalRounds.total s c
    obtain ⟨last,r,i,hl,hp,hc⟩ := ih out out (U8.wrapping_add round 1#u8) hcan
    refine ⟨last,r,i,?_,?_,hc⟩
    · simp only [PV_RunJoin_SourceInternalRounds.steps,ho,bind_tc_ok,poseidon2.merkle_node_compress_v3.closure.Insts.CoreOpsFunctionFnMutTuplePoseidon2RoundTransitionTuple.call_mut,hl]
      rfl
    · simp only [internal,ho,bind_tc_ok,hp]

#print axioms full_total_threaded
#print axioms internal_total_threaded
end R1Z.PV_RunJoin_ParentRoundTotal
