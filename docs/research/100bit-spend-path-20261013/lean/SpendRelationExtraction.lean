import R1SpendRelation
import R1InputWitness
import R1SpendSemantics

/-! Reuse the existing production-trace witness facts for the explicit spend
relation. This existential bridge does not implement the list decoder, field
descent, or the full-log efficient extractor. -/
set_option autoImplicit false
namespace AspisR1.SpendRelationExtraction

open R0P SpendRelation
variable {K : Type} [Field K] [DecidableEq K]

attribute [local irreducible] poseidonPermutation nodeCompress merkleRoot

theorem of_production (prime : Nat) [CharP K prime]
    (hprime : prime = 2^31 - 1) (pub : Public K) (A : Trace K) (lam chi : K)
    (hshape : PublicOptionShape.canonical pub)
    (h : ProductionHolds pub lam chi A ∧ CopyLinkBalance pub A) :
    ∃ w : Witness K, Rspend pub w := by
  obtain ⟨v0, v1, v2, h0, h1, h2, hbalance, e0, e1, e2, hinput⟩ :=
    InputWitness.bounded_of_production prime hprime pub A lam chi h
  have hfacts := SpendSemantics.of_production prime hprime pub A lam chi h
  let w : Witness K :=
    { inputValue := ⟨v0, h0⟩
      outputValue := ⟨v1, h1⟩
      changeValue := ⟨v2, h2⟩
      sk := traceSk A
      salt := traceSalt A
      path := tracePath A
      pair := InputPair.leaf A
      recipientOwner := OutputNotes.chunk A 27
      recipientSalt := OutputNotes.salt A 28 29
      changeOwner := OutputNotes.chunk A 30
      changeSalt := OutputNotes.salt A 31 32 }
  refine ⟨w, hshape, hinput, hbalance, ?_, ?_⟩
  · simpa only [changeCommitment, w, e2] using hfacts.change
  · cases hv : pub.variant with
    | privateTransfer =>
        obtain ⟨recipient, hr, _⟩ :=
          PublicOptionShape.private_transfer_shape pub hv hshape
        change variantOutput pub w
        rw [variantOutput, hv]
        rw [hr]
        apply congrArg some
        simpa only [recipientCommitment, w, e1] using hfacts.recipient hv recipient hr
    | withdrawal =>
        obtain ⟨amount, _, ha, _⟩ := PublicOptionShape.withdrawal_shape pub hv hshape
        change variantOutput pub w
        rw [variantOutput, hv]
        rw [ha]
        apply congrArg some
        exact (hfacts.withdrawal hv amount ha).symm.trans e1

#print axioms of_production
end AspisR1.SpendRelationExtraction
