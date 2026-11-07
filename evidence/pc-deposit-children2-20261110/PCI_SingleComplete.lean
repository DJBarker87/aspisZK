import PCI_SingleValidation
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_SingleComplete
open PCA

def source (commitment : Digest) : Result (Except LeafError PairWitness) := do
  let valid ← PCI_ValidateComplete.source (PCC.singleWitness commitment)
  match valid with
  | .ok () => ok (.ok (PCC.singleWitness commitment))
  | .error e => ok (.error e)

theorem complete (commitment : Digest) :
    source commitment=ok (if PCC.canonical commitment then
      Except.ok (PCC.singleWitness commitment) else Except.error .NonCanonicalCommitment) := by
  simp only [source,PCI_ValidateComplete.complete,PCI_SingleValidation.validation]
  cases h : PCC.canonical commitment <;> simp [h]

def observe (commitment : Digest) (state : PCA_State) : Result (Execution PairWitness) :=
  match source commitment with
  | .ok out => .ok {state,events:=[],reply:=match out with
      | Except.ok witness => Outcome.ok witness
      | Except.error e => Outcome.error (.leaf e)}
  | .fail e => .fail e
  | .div => .div

theorem result_state_effects (commitment : Digest) (state : PCA_State) :
    observe commitment state=ok (PCC.singleOutputReference commitment state) := by
  simp only [observe,complete,PCC.singleOutputReference,PCI_SingleValidation.validation]
  cases h : PCC.canonical commitment <;> simp [h]

#print axioms complete
#print axioms result_state_effects
end PCI_SingleComplete
