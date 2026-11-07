import PV_THR2_Spawn361HookTrueReached
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361HookFalsePrefixReached
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Actual12402–12405 creates two references to the existing Thread local. -/
def prepared (s : Store Data) (a : Nat) :=
  write (write (write (write s ⟨a,15,[]⟩ none) ⟨a,16,[]⟩ none)
    ⟨a,16,[]⟩ (some (PV_STX2_TypedReferences.reference ⟨a,10,[]⟩ .null)))
    ⟨a,15,[]⟩ (some (PV_STX2_TypedReferences.reference ⟨a,10,[]⟩ .null))
/-- Internal false-arm control and freshness. Compose the retained prefix
without constraining the arbitrary child payload; amended-translator conditional. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.block51 ++ PV_THR2_F361.live.body.drop 41) c)
    (fresh : c.frame.activation < c.store.nextActivation)
 :
    ∃ d, (PV_THR2_Source361HookFalsePrefix.after (PV_THR2_OwnInitExactReturnedCases.carrier C b) q).current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.block51.drop 4 ++ PV_THR2_F361.live.body.drop 41) d ∧
      (∀ i, i ≠ 15 → i ≠ 16 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      d.store.cells ⟨d.frame.activation,15,[]⟩ = some (PV_STX2_TypedReferences.reference ⟨d.frame.activation,10,[]⟩ .null) := by
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases running
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases ready with ⟨rfl,rfl,rfl,rfl⟩
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  have isReady : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.block51 ++ PV_THR2_F361.live.body.drop 41)
      ⟨{activation := a,remaining := (PV_THR2_F361.block51 ++ PV_THR2_F361.live.body.drop 41),loops := loops},parents,s⟩ := ⟨rfl,rfl,rfl,rfl⟩
  have result : PV_THR2_IntrinsicFrameChain.result B a parents loops (PV_THR2_F361.block51.drop 4 ++ PV_THR2_F361.live.body.drop 41)
      w PV_THR2_Source361HookFalsePrefix.chain s =
      .running ⟨{activation := a,remaining := (PV_THR2_F361.block51.drop 4 ++ PV_THR2_F361.live.body.drop 41),loops := loops},parents,prepared s a⟩ := by
    have metadata : B.constant (.object [("kind",.object [("Adt",.array [.null,.array []])]),
        ("ty",.object [("Deduplicated",.number 646)])]) = some .null := rfl
    have reference (p : Address) : B.reference p .null = PV_STX2_TypedReferences.reference p .null := rfl
    have deref : B.dereference w (PV_STX2_TypedReferences.reference ⟨a,10,[]⟩ .null) = some ⟨a,10,[]⟩ :=
      PV_STX2_TypedReferences.dereference
        (PV_THR2_FunctionValues.base (PV_THR2_KeyInstall.carrier (PV_THR2_ThreadFields.carrier
          (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier C))) b)) w ⟨a,10,[]⟩ .null
    have completedConstant : (PV_THR2_AggregateCompletion.carrier B).constant = B.constant := rfl
    have completedDeref : (PV_THR2_AggregateCompletion.carrier B).dereference = B.dereference := rfl
    have completedReference : (PV_THR2_AggregateCompletion.carrier B).reference = B.reference := rfl
    simp [PV_THR2_Source361HookFalsePrefix.chain,PV_THR2_Source15CaptureChain.prepend,
      PV_THR2_F361.node43,PV_THR2_F361.node44,PV_THR2_F361.node45,PV_THR2_F361.node46,
      PV_THR2_IntrinsicFrameChain.result,PV_THR2_IntrinsicFrameChain.bound,
      PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,
      write,prepared,metadata,reference,deref,completedConstant,completedDeref,completedReference]
  change ∃ d, (PV_THR2_Source361HookFalsePrefix.after B _).current.status = .running d ∧ _
  simp only [PV_THR2_Source361HookFalsePrefix.after,PV_THR2_IntrinsicAtContinuation.after,if_pos isReady,
    PV_THR2_Source361HookFalsePrefix.finish]
  rw [result]
  refine ⟨_,rfl,?_,⟨rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · exact fresh
  · intro i n15 n16; simp [prepared,write,n15,n16]
  · simp [prepared,write]
#print axioms after
end PV_THR2_Spawn361HookFalsePrefixReached
