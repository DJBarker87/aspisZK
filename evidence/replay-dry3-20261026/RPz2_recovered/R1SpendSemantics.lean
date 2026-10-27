import R1SpendValues
import R1OutputNotes
import R0P.SemAssembly

set_option autoImplicit false

namespace AspisR1.SpendSemantics

open R0P

variable {K : Type} [Field K]

/-- Production value, input-note extraction, and output-note bindings. This
statement does not include a public append update, public `Option` shape,
strict output positivity, ROM condition, Rust correspondence, or privacy claim. -/
structure NoteFacts (pub : Public K) (A : Trace K) : Prop where
  values : SpendValues.BoundedBalanced A
  input : InputNoteExtracted pub A
  change : pub.change =
    noteCommitment (OutputNotes.chunk A 30) (A 10 1012) pub.assetId (OutputNotes.salt A 31 32)
  recipient : pub.variant = .privateTransfer →
    ∀ r : Digest K, pub.recipient = some r →
      r = noteCommitment (OutputNotes.chunk A 27) (A 10 1010) pub.assetId
        (OutputNotes.salt A 28 29)
  withdrawal : pub.variant = .withdrawal →
    ∀ amount, pub.withdrawalAmount = some amount → A 10 1010 = amount

theorem of_production (prime : Nat) [CharP K prime]
    (hprime : prime = 2 ^ 31 - 1) (pub : Public K) (A : Trace K)
    (lam chi : K) (h : ProductionHolds pub lam chi A ∧ CopyLinkBalance pub A) :
    NoteFacts pub A := by
  have values := SpendValues.of_value_balance prime hprime pub A h.1.1 h.2
  have input := semantic_extraction pub A lam chi h (extraction_step pub lam chi A)
  have hasset : Holds assetFamily pub A := h.1.2.2.1
  have hschedule : Holds scheduleFamily pub A := h.1.2.2.2.1
  have hdigest : Holds digestFamily pub A := h.1.2.2.2.2.2.1
  have hposeidon : Holds poseidonScalarFamily pub A := h.1.2.2.2.2.2.2.1
  have hassetFacts := (asset_holds_iff pub A).mp hasset
  refine ⟨values, input,
    OutputNotes.change_public pub A hschedule hasset hdigest hposeidon h.2,
    ?_, ?_⟩
  · intro hvariant r hpresent
    exact OutputNotes.recipient_public pub A hvariant r hpresent
      hschedule hasset hdigest hposeidon h.2
  · exact hassetFacts.2.2.2

#print axioms of_production

end AspisR1.SpendSemantics
