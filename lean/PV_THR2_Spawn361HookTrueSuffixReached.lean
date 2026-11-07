import PV_THR2_Spawn361HookTrueReached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361HookTrueSuffixReached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Source12400 marks the selected hook payload live. -/
def prepared (s : Store Data) (a : Nat) := write s ⟨a,65,[]⟩ (some (.boolean true))
/-- Internal true-child output control and freshness. Compose the retained suffix
without constraining the arbitrary child payload; amended-translator conditional. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.block42.drop 1 ++ PV_THR2_F361.live.body.drop 41) c)
    (fresh : c.frame.activation < c.store.nextActivation)
 :
    ∃ d, (PV_THR2_Source361HookTrueSuffix.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 41) d ∧
      (∀ i, i ≠ 65 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      d.store.cells ⟨d.frame.activation,65,[]⟩ = some (.boolean true) := by
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.block42.drop 1 ++ PV_THR2_F361.live.body.drop 41)
      ⟨{activation := a,remaining := (PV_THR2_F361.block42.drop 1 ++ PV_THR2_F361.live.body.drop 41),loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have result : PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.live.body.drop 41)
      w PV_THR2_Source361HookTrueSuffix.chain s =
      .running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 41,loops := loops},parents,prepared s a⟩ := by
    have flag : B.constant (.object [("kind",.object [("Literal",.object [("Bool",.boolean true)])]),
        ("ty",.object [("Deduplicated",.number 556)])]) = some (.boolean true) := rfl
    have completedConstant : (PV_THR2_AggregateCompletion.carrier B).constant = B.constant := rfl
    simp [PV_THR2_Source361HookTrueSuffix.chain,PV_THR2_Source15CaptureChain.prepend,
      PV_THR2_F361.node41,
      PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
      PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      write,prepared,flag,completedConstant]
  change ∃ d, (PV_THR2_Source361HookTrueSuffix.after B _).current.status = .running d ∧ _
  simp only [PV_THR2_Source361HookTrueSuffix.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361HookTrueSuffix.finish]
  rw [result]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · exact fresh
  · intro i n65; simp [prepared,write,n65]
  · simp [prepared,write]
#print axioms after
end PV_THR2_Spawn361HookTrueSuffixReached
