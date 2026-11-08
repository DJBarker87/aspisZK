import PV_THR2_Spawn361HooksJoined
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361PacketPrefixReached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Actual12515–12522 prepares the packet and moves the scope argument. -/
def prepared (s : Store Data) (a : Nat) (scope : Data) :=
  write (write (write (write (write (write (write (write (write (s) ⟨a,14,[]⟩ (none)) ⟨a,17,[]⟩ (none)) ⟨a,18,[]⟩ (none)) ⟨a,19,[]⟩ (none)) ⟨a,67,[]⟩ (some (.boolean false))) ⟨a,4,[]⟩ (none)) ⟨a,19,[]⟩ (some scope)) ⟨a,20,[]⟩ (none)) ⟨a,21,[]⟩ (none)
/-- Internal actual drop41 control and source scope cell.
Only the retained eight-instruction segment is reduced; arbitrary stores remain symbolic. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config) (scope : Data)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 41) c)
    (fresh : c.frame.activation < c.store.nextActivation)
    (hooksCell : c.store.cells ⟨c.frame.activation,4,[]⟩ = some scope) :
    ∃ d, (PV_THR2_Source361Chain41To49.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 49) d ∧
      (∀ i, i ≠ 4 → i ≠ 14 → i ≠ 17 → i ≠ 18 → i ≠ 19 → i ≠ 20 → i ≠ 21 → i ≠ 67 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      d.store.cells ⟨d.frame.activation,19,[]⟩ = some scope := by
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  change s.cells ⟨a,4,[]⟩ = some scope at hooksCell
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 41)
      ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 41,loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have result : PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.live.body.drop 49)
      w PV_THR2_Source361Chain41To49.chain s =
      .running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 49,loops := loops},parents,prepared s a scope⟩ := by
    have flag : B.constant (.object [("kind",.object [("Literal",.object [("Bool",.boolean false)])]),
      ("ty",.object [("Deduplicated",.number 556)])]) = some (.boolean false) := rfl
    have completedConstant : (PV_THR2_AggregateCompletion.carrier B).constant = B.constant := rfl
    simp [PV_THR2_Source361Chain41To49.chain,PV_THR2_Source15CaptureChain.prepend,
      PV_THR2_F361.node53,PV_THR2_F361.node54,PV_THR2_F361.node55,PV_THR2_F361.node56,PV_THR2_F361.node57,PV_THR2_F361.node58,PV_THR2_F361.node59,PV_THR2_F361.node60,
      PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
      PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      hooksCell,write,prepared,flag,completedConstant]
  change ∃ d, (PV_THR2_Source361Chain41To49.after B _).current.status = .running d ∧ _
  simp only [PV_THR2_Source361Chain41To49.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361Chain41To49.finish]
  rw [result]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · exact fresh
  · intro i n4 n14 n17 n18 n19 n20 n21 n67; simp [prepared,write,n4,n14,n17,n18,n19,n20,n21,n67]
  · simp [prepared,write]
#print axioms after
end PV_THR2_Spawn361PacketPrefixReached
