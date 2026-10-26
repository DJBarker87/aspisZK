import SCJ_OrderedTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_OrderObstruction
open FS FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open SCI_Projection.OrderWitness
/-- Exactly the missing first-order property in the retained deletion witness. -/
theorem sublist_not_first_order :
    ∃ small full : List (Bytes × State), small.Sublist full ∧
      Before small address [] ∧ ¬ Before full address [] := by
  refine ⟨[(address,two),([],one)],[([],one),(address,two),([],one)],
    List.Sublist.cons _ (List.Sublist.refl _),?_,?_⟩
  · simp [Before,Read,firstIdx,nonempty]
  · simp [Before,Read,firstIdx,nonempty]

#print axioms sublist_not_first_order
end AspisR1.SCJ_OrderObstruction
end
