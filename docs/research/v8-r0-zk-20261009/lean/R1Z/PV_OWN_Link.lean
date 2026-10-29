import Init
set_option autoImplicit false
namespace R1Z.PV_OWN_Link
inductive Kind where
 | spongeCarry («from» to : UInt8)
 | ownerOutput | nullifierKey | inputSaltHead | inputSaltTail
 | privatePathCurrent (level : UInt8) | privatePathLeft (level : UInt8) | privatePathRight (level : UInt8)
 | valueSource (value : UInt8)
 | conservationInput | conservationRecipient | conservationChange | conservationPartial
 | inputSecondCommitment | inputSelectedSide | outputSecondCommitment | outputPairFirst
 | outputPairFirstWithdrawal | outputPairSecond
 | appendCurrentLeft (level : UInt8) | appendCurrentRight (level : UInt8)
 deriving DecidableEq
structure Link where
 kind : Kind
 producer : UInt16
 consumer : UInt16
 deriving DecidableEq
/-- The full kind survives a row relocation. ABI byte encoding is not inferred. -/
def relocate (link : Link) (producer consumer : UInt16) : Link :=
 {link with producer := producer, consumer := consumer}
theorem kind_retained (link : Link) (p c : UInt16) : (relocate link p c).kind=link.kind := rfl
/-- Erasing kind cannot be the byte-memory refinement carrier. -/
theorem endpoint_projection_not_injective :
 ∃ a b : Link, (a.producer,a.consumer)=(b.producer,b.consumer) ∧ a≠b := by
 refine ⟨⟨.ownerOutput,0,0⟩,⟨.nullifierKey,0,0⟩,rfl,?_⟩
 intro h
 have hh:=congrArg Link.kind h
 cases hh
#print axioms kind_retained
#print axioms endpoint_projection_not_injective
end R1Z.PV_OWN_Link
