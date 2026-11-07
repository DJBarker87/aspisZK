import PV_THR2_Spawn361MetadataChild70Reached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361MetadataStorage71Reached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Source13124–13128 prepares the metadata aggregate and its live flags. -/
def prepared (s : Store Data) (a : Nat) :=
  write (write (write (write (write s ⟨a,26,[]⟩ none) ⟨a,27,[]⟩ none)
    ⟨a,65,[]⟩ (some (.boolean false))) ⟨a,64,[]⟩ (some (.boolean false)))
    ⟨a,63,[]⟩ (some (.boolean true))
/-- Internal child12668 output control and freshness. Compose the retained suffix
without constraining the arbitrary child payload; amended-translator conditional. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 71) c)
    (fresh : c.frame.activation < c.store.nextActivation)
 :
    ∃ d, (PV_THR2_Source361Chain71To76.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 76) d ∧
      (∀ i, i ≠ 26 → i ≠ 27 → i ≠ 63 → i ≠ 64 → i ≠ 65 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) := by
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 71)
      ⟨{activation := a,remaining := (PV_THR2_F361.live.body.drop 71),loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have result : PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.live.body.drop 76)
      w PV_THR2_Source361Chain71To76.chain s =
      .running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 76,loops := loops},parents,prepared s a⟩ := by
    have literal (v : Bool) : B.constant (.object [("kind",.object [("Literal",.object [("Bool",.boolean v)])]),
        ("ty",.object [("Deduplicated",.number 556)])]) = some (.boolean v) := rfl
    have completedConstant : (PV_THR2_AggregateCompletion.carrier B).constant = B.constant := rfl
    simp [PV_THR2_Source361Chain71To76.chain,PV_THR2_Source15CaptureChain.prepend,
      PV_THR2_F361.node83,PV_THR2_F361.node84,PV_THR2_F361.node85,
      PV_THR2_F361.node86,PV_THR2_F361.node87,
      PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
      PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      write,prepared,literal,completedConstant]
  change ∃ d, (PV_THR2_Source361Chain71To76.after B _).current.status = .running d ∧ _
  simp only [PV_THR2_Source361Chain71To76.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361Chain71To76.finish]
  rw [result]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_⟩
  · exact fresh
  · intro i n26 n27 n63 n64 n65; simp [prepared,write,n26,n27,n63,n64,n65]
#print axioms after
end PV_THR2_Spawn361MetadataStorage71Reached
