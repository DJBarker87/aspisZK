import PV_THR2_Spawn361MetadataAggregate76Reached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361MetadataReference77Reached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Source13131–13134 references the retained packet at local17. -/
def prepared (s : Store Data) (a : Nat) :=
  write (write (write (write s ⟨a,28,[]⟩ none) ⟨a,29,[]⟩ none) ⟨a,30,[]⟩ none)
    ⟨a,30,[]⟩ (some (PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null))
/-- Internal actual drop59 control and freshness. Compose the retained prefix
without constraining the arbitrary child payload; amended-translator conditional. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 77) c)
    (fresh : c.frame.activation < c.store.nextActivation)
 :
    ∃ d, (PV_THR2_Source361Chain77To81.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 81) d ∧
      (∀ i, i ≠ 28 → i ≠ 29 → i ≠ 30 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      d.store.cells ⟨d.frame.activation,30,[]⟩ = some (PV_STX2_TypedReferences.reference ⟨d.frame.activation,17,[]⟩ .null) := by
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 77)
      ⟨{activation := a,remaining := (PV_THR2_F361.live.body.drop 77),loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have result : PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.live.body.drop 81)
      w PV_THR2_Source361Chain77To81.chain s =
      .running ⟨{activation := a,remaining := (PV_THR2_F361.live.body.drop 81),loops := loops},parents,prepared s a⟩ := by
    have metadata : B.constant (.object [("kind",.object [("Adt",.array [.null,.array []])]),
        ("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
    have reference (p : Address) : B.reference p .null = PV_STX2_TypedReferences.reference p .null := rfl
    have completedConstant : (PV_THR2_AggregateCompletion.carrier B).constant = B.constant := rfl
    have completedReference : (PV_THR2_AggregateCompletion.carrier B).reference = B.reference := rfl
    simp [PV_THR2_Source361Chain77To81.chain,PV_THR2_Source15CaptureChain.prepend,
      PV_THR2_F361.node89,PV_THR2_F361.node90,PV_THR2_F361.node91,PV_THR2_F361.node92,
      PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
      PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      write,prepared,metadata,reference,completedConstant,completedReference]
  change ∃ d, (PV_THR2_Source361Chain77To81.after B _).current.status = .running d ∧ _
  simp only [PV_THR2_Source361Chain77To81.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361Chain77To81.finish]
  rw [result]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · exact fresh
  · intro i n28 n29 n30; simp [prepared,write,n28,n29,n30]
  · simp [prepared,write]
#print axioms after
end PV_THR2_Spawn361MetadataReference77Reached
