import PV_THR2_TypedRepresentation_PacketRef
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361PacketField82Reached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Source13324–13325 constructs the first field's address. It does not read
that field or assume that the arbitrary returned address resolves in the store. -/
def prepared (s : Store Data) (a : Nat) (p : Address) :=
  write (write s ⟨a,30,[]⟩ none) ⟨a,28,[]⟩
    (some (PV_STX2_TypedReferences.reference {p with fields := p.fields ++ [0]} .null))
/-- Internal actual drop59 control and freshness. Compose the retained prefix
without constraining the arbitrary child payload; amended-translator conditional. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config) (p : Address)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 82) c)
    (fresh : c.frame.activation < c.store.nextActivation)
    (referenceCell : c.store.cells ⟨c.frame.activation,29,[]⟩ =
      some (PV_STX2_TypedReferences.reference p .null))
 :
    ∃ d, (PV_THR2_Source361Chain82To84.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 84) d ∧
      (∀ i, i ≠ 28 → i ≠ 30 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      d.store.cells ⟨d.frame.activation,28,[]⟩ = some
        (PV_STX2_TypedReferences.reference {p with fields := p.fields ++ [0]} .null) := by
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  change s.cells ⟨a,29,[]⟩ = some (PV_STX2_TypedReferences.reference p .null) at referenceCell
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 82)
      ⟨{activation := a,remaining := (PV_THR2_F361.live.body.drop 82),loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have result : PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.live.body.drop 84)
      w PV_THR2_Source361Chain82To84.chain s =
      .running ⟨{activation := a,remaining := (PV_THR2_F361.live.body.drop 84),loops := loops},parents,prepared s a p⟩ := by
    have metadata : B.constant (.object [("kind",.object [("Adt",.array [.null,.array []])]),
        ("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
    have dereference (address : Address) : B.dereference w (PV_STX2_TypedReferences.reference address .null) = some address :=
      PV_STX2_TypedReferences.dereference _ _ _ _
    have reference (p : Address) : B.reference p .null = PV_STX2_TypedReferences.reference p .null := rfl
    have completedConstant : (PV_THR2_AggregateCompletion.carrier B).constant = B.constant := rfl
    have completedReference : (PV_THR2_AggregateCompletion.carrier B).reference = B.reference := rfl
    simp [PV_THR2_Source361Chain82To84.chain,PV_THR2_Source15CaptureChain.prepend,
      PV_THR2_F361.node94,PV_THR2_F361.node95,
      PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
      PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      write,prepared,metadata,reference,completedConstant,completedReference,referenceCell,dereference]
  change ∃ d, (PV_THR2_Source361Chain82To84.after B _).current.status = .running d ∧ _
  simp only [PV_THR2_Source361Chain82To84.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361Chain82To84.finish]
  rw [result]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · exact fresh
  · intro i n28 n30; simp [prepared,write,n28,n30]
  · simp [prepared,write]
#print axioms after
end PV_THR2_Spawn361PacketField82Reached
