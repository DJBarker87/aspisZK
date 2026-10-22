import R1Z.ProverCommitTrustedStd24
import R1Z.ProverCommitTreeMap22
import R1Z.ProverCommitPublish43
/-! A return-only extraction cannot certify ProgramOne's shared mutation.
This is an interface countermodel, not a counterexample to Rust RefCell.
Both interpretations use the identical lawful map and TLS implementation. -/
set_option autoImplicit false
namespace R1Z.ProverCommitEffectGap45
open ProverCommitTrustedStd24
abbrev Table := Std.TreeMap Nat Nat compare

def initial : Table := (∅ : Table).insert 0 0

def expected : Nat × Table × Bool :=
  let next := ProverCommitTreeMap22.program initial 0 1 false
  (1,next.1,next.2)

def erased : Nat × Table × Bool := (1,initial,false)

/-- Every accepted library law can hold while equal digest return values
leave different table entries and a different sticky collision flag. -/
theorem returned_digest_does_not_identify_effects :
    TrustedStd (modelMap (Key := Nat) (Value := Nat) (cmp := compare))
      (modelTLS (Thread := Unit) (Slot := Unit) (Output := Unit)) () [] ∧
    expected.1=erased.1 ∧
    expected.2.1[0]?=some 1 ∧ erased.2.1[0]?=some 0 ∧
    expected.2.2=true ∧ erased.2.2=false := by
  refine ⟨model_consistent (),rfl,?_,?_,?_,rfl⟩
  · simp [expected,ProverCommitTreeMap22.program]
  · simp [erased,initial]
  · simp [expected,ProverCommitTreeMap22.program,initial,ProverCommitTable20.conflict]

/-- Dropping precisely that effect changes the native final Merkle guard
from an error to published bytes/table. Equal digest outputs do not transport
D143's published-data observable. -/
theorem publication_differs :
    ProverCommitPublish43.finish (.ok []) (.ok true) expected.2.2
      (.ok expected.2.1) = .error .merkle ∧
    ProverCommitPublish43.finish (.ok []) (.ok true) erased.2.2
      (.ok erased.2.1) = .ok ([],initial) := by
  have h := returned_digest_does_not_identify_effects
  constructor
  · rw [h.2.2.2.2.1]
    rfl
  · rfl

#print axioms returned_digest_does_not_identify_effects
#print axioms publication_differs
end R1Z.ProverCommitEffectGap45
