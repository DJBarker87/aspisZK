import Init
set_option autoImplicit false
namespace NEF
/-- Complete abstract execution outcome; state and ordered effects are explicit. -/
structure Outcome (R S E : Type) where
  result : R
  state : S
  effects : List E
  deriving DecidableEq

def mark {P S E : Type} (obs : Option (P → S → S × List E)) (p : P)
    (s : S) : Unit × S × List E :=
  match obs with
  | none => ((), s, [])
  | some f => let (s', es) := f p s; ((), s', es)

theorem mark_none {P S E : Type} (p : P) (s : S) :
    @mark P S E none p s = ((), s, []) := rfl

def continueAfterMark {P R S E : Type} (obs : Option (P → S → S × List E))
    (p : P) (s : S) (k : S → Outcome R S E) : Outcome R S E :=
  let (_, s', es) := mark obs p s
  let out := k s'
  {out with effects := es ++ out.effects}

theorem mark_none_context {P R S E : Type} (p : P) (s : S)
    (k : S → Outcome R S E) : continueAfterMark none p s k = k s := rfl

theorem mark_none_preserves_result {P R S E : Type} (p : P) (s : S)
    (k : S → Outcome R S E) : (continueAfterMark none p s k).result = (k s).result := rfl

theorem mark_none_preserves_state {P R S E : Type} (p : P) (s : S)
    (k : S → Outcome R S E) : (continueAfterMark none p s k).state = (k s).state := rfl

theorem mark_none_preserves_effects {P R S E : Type} (p : P) (s : S)
    (k : S → Outcome R S E) : (continueAfterMark none p s k).effects = (k s).effects := rfl
#print axioms mark_none
#print axioms mark_none_context
#print axioms mark_none_preserves_result
#print axioms mark_none_preserves_state
#print axioms mark_none_preserves_effects
end NEF
