import PV_THR2_Spawn361PacketChild63Reached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361MetadataMove64Reached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Source12951–12956 retains Boolean flags and moves captured local5 to26. -/
def prepared (s : Store Data) (a : Nat) (captured : Data) :=
  write (write (write (write (write (write (write s
    ⟨a,64,[]⟩ (some (.boolean true))) ⟨a,24,[]⟩ none) ⟨a,25,[]⟩ none)
    ⟨a,26,[]⟩ none) ⟨a,66,[]⟩ (some (.boolean false))) ⟨a,5,[]⟩ none)
    ⟨a,26,[]⟩ (some captured)
/-- Internal actual drop59 control and freshness. Compose the retained prefix
without constraining the arbitrary child payload; amended-translator conditional. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config) (captured : Data)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 64) c)
    (fresh : c.frame.activation < c.store.nextActivation)
    (closureCell : c.store.cells ⟨c.frame.activation,5,[]⟩ = some captured)
 :
    ∃ d, (PV_THR2_Source361Chain64To70.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 70) d ∧
      (∀ i, i ≠ 5 → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 64 → i ≠ 66 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      d.store.cells ⟨d.frame.activation,26,[]⟩ = some captured := by
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  change s.cells ⟨a,5,[]⟩ = some captured at closureCell
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 64)
      ⟨{activation := a,remaining := (PV_THR2_F361.live.body.drop 64),loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have result : PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.live.body.drop 70)
      w PV_THR2_Source361Chain64To70.chain s =
      .running ⟨{activation := a,remaining := (PV_THR2_F361.live.body.drop 70),loops := loops},parents,prepared s a captured⟩ := by
    have literal (v : Bool) : B.constant (.object [("kind",.object [("Literal",.object [("Bool",.boolean v)])]),
        ("ty",.object [("Deduplicated",.number 556)])]) = some (.boolean v) := rfl
    have completedConstant : (PV_THR2_AggregateCompletion.carrier B).constant = B.constant := rfl
    simp [PV_THR2_Source361Chain64To70.chain,PV_THR2_Source15CaptureChain.prepend,
      PV_THR2_F361.node76,PV_THR2_F361.node77,PV_THR2_F361.node78,
      PV_THR2_F361.node79,PV_THR2_F361.node80,PV_THR2_F361.node81,
      PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
      PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      write,prepared,literal,completedConstant,closureCell]
  change ∃ d, (PV_THR2_Source361Chain64To70.after B _).current.status = .running d ∧ _
  simp only [PV_THR2_Source361Chain64To70.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361Chain64To70.finish]
  rw [result]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · exact fresh
  · intro i n5 n24 n25 n26 n64 n66; simp [prepared,write,n5,n24,n25,n26,n64,n66]
  · simp [prepared,write]
#print axioms after
end PV_THR2_Spawn361MetadataMove64Reached
