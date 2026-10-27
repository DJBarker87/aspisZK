import CurrentCompactFirstCompositionV1
set_option autoImplicit false
namespace RPz7_PhaseIso
open AspisR1PublicPreparation
/-- Retain the old S1 kernel carrier; the producer owns verifier.Phase. -/
abbrev Phase := FirstCaller.Phase

def toFirst : verifier.Phase → Phase
  | .Parsed => .Parsed
  | .Semantic => .Semantic
  | .SemanticPart i => .SemanticPart i
  | .Prepare => .Prepare
  | .CheckpointRead => .CheckpointRead
  | .Merkle i => .Merkle i
  | .Query i => .Query i
  | .QueryPart i j => .QueryPart i j
  | .CheckpointWrite => .CheckpointWrite
  | .Relation => .Relation
  | .Final => .Final

def toVerifier : Phase → verifier.Phase
  | .Parsed => .Parsed
  | .Semantic => .Semantic
  | .SemanticPart i => .SemanticPart i
  | .Prepare => .Prepare
  | .CheckpointRead => .CheckpointRead
  | .Merkle i => .Merkle i
  | .Query i => .Query i
  | .QueryPart i j => .QueryPart i j
  | .CheckpointWrite => .CheckpointWrite
  | .Relation => .Relation
  | .Final => .Final

theorem first_roundtrip_RPz7 (p : Phase) : toFirst (toVerifier p) = p := by
  cases p <;> rfl

theorem verifier_roundtrip_RPz7 (p : verifier.Phase) : toVerifier (toFirst p) = p := by
  cases p <;> rfl

def phaseEquiv : verifier.Phase ≃ Phase where
  toFun := toFirst
  invFun := toVerifier
  left_inv := verifier_roundtrip_RPz7
  right_inv := first_roundtrip_RPz7

/-- Contravariant callback transport; applies to every result/effect type. -/
def callbackToVerifier {R : Type} (f : Phase → R) : verifier.Phase → R :=
  fun p => f (toFirst p)
def callbackToFirst {R : Type} (f : verifier.Phase → R) : Phase → R :=
  fun p => f (toVerifier p)

theorem callback_first_roundtrip_RPz7 {R : Type} (f : Phase → R) :
    callbackToFirst (callbackToVerifier f) = f := by
  funext p
  exact congrArg f (first_roundtrip_RPz7 p)
theorem callback_verifier_roundtrip_RPz7 {R : Type} (f : verifier.Phase → R) :
    callbackToVerifier (callbackToFirst f) = f := by
  funext p
  exact congrArg f (verifier_roundtrip_RPz7 p)

def observerToVerifier {R : Type} (obs : Option (Phase → R)) :
    Option (verifier.Phase → R) := obs.map callbackToVerifier
def observerToFirst {R : Type} (obs : Option (verifier.Phase → R)) :
    Option (Phase → R) := obs.map callbackToFirst

theorem observer_first_roundtrip_RPz7 {R : Type} (obs : Option (Phase → R)) :
    observerToFirst (observerToVerifier obs) = obs := by
  cases obs with
  | none => rfl
  | some f => exact congrArg some (callback_first_roundtrip_RPz7 f)
theorem observer_verifier_roundtrip_RPz7 {R : Type}
    (obs : Option (verifier.Phase → R)) :
    observerToVerifier (observerToFirst obs) = obs := by
  cases obs with
  | none => rfl
  | some f => exact congrArg some (callback_verifier_roundtrip_RPz7 f)

theorem observer_none_RPz7 {R : Type} :
    observerToVerifier (R := R) none = none := rfl
theorem observer_some_RPz7 {R : Type} (f : Phase → R) :
    observerToVerifier (some f) = some (fun p => f (toFirst p)) := rfl

/-- Transport of any observer-consuming function, including partially applied
Finish, mark, verify, finish and their code/budget/source consumers. -/
def consumerToVerifier {R S : Type} (f : Option (Phase → R) → S) :
    Option (verifier.Phase → R) → S := fun obs => f (observerToFirst obs)
def consumerToFirst {R S : Type} (f : Option (verifier.Phase → R) → S) :
    Option (Phase → R) → S := fun obs => f (observerToVerifier obs)

theorem consumer_first_roundtrip_RPz7 {R S : Type} (f : Option (Phase → R) → S) :
    consumerToFirst (consumerToVerifier f) = f := by
  funext obs
  exact congrArg f (observer_first_roundtrip_RPz7 obs)
theorem consumer_verifier_roundtrip_RPz7 {R S : Type}
    (f : Option (verifier.Phase → R) → S) :
    consumerToVerifier (consumerToFirst f) = f := by
  funext obs
  exact congrArg f (observer_verifier_roundtrip_RPz7 obs)

theorem evaluation_RPz7 {R : Type} (f : Phase → R) (p : Phase) :
    callbackToVerifier f (toVerifier p) = f p :=
  congrArg f (first_roundtrip_RPz7 p)

#print axioms phaseEquiv
#print axioms first_roundtrip_RPz7
#print axioms verifier_roundtrip_RPz7
#print axioms callback_first_roundtrip_RPz7
#print axioms callback_verifier_roundtrip_RPz7
#print axioms observer_first_roundtrip_RPz7
#print axioms observer_verifier_roundtrip_RPz7
#print axioms observer_none_RPz7
#print axioms observer_some_RPz7
#print axioms consumer_first_roundtrip_RPz7
#print axioms consumer_verifier_roundtrip_RPz7
#print axioms evaluation_RPz7
end RPz7_PhaseIso
