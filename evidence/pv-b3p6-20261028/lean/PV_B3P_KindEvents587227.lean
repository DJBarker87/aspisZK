import PV_B3P_DominatedEvents578227
namespace PV_B3P_KindEvents587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227
set_option autoImplicit false
def kind0 : Fin 5 := ⟨0,by decide⟩
def kind1 : Fin 5 := ⟨1,by decide⟩
def kind2 : Fin 5 := ⟨2,by decide⟩
def kind3 : Fin 5 := ⟨3,by decide⟩
def kind4 : Fin 5 := ⟨4,by decide⟩
/-- Project a completed source literal initializer and successful array read.
An invalid array read has no downstream link_weight observation. Native
initialization, pointer reads and failure observability are separate. -/
def sourceEvent (table : List (Fin 5)) (index : Nat) (effects : List (Result Unit)) :
    Result (Option IndexState) :=
  match table[index]? with
  | none => .ok none
  | some kind => through effects (some ⟨kind.val,5⟩)

def sourceCondition (observed : IndexState) : Bool :=
  decide (observed.index = 0 ∨ observed.index = 1 ∨ observed.index = 2 ∨
    observed.index = 3 ∨ observed.index = 4)

theorem event_guard (table : List (Fin 5)) (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent table index effects = .ok (some observed)) :
    sourceCondition observed = true := by
  cases found : table[index]? with
  | none => simp only [sourceEvent,found] at ran; cases ran
  | some kind =>
    simp only [sourceEvent,found] at ran
    have frame := through_value _ _ _ ran
    cases frame
    change decide (kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 ∨ kind.val = 3 ∨ kind.val = 4) = true
    apply decide_eq_true
    have bounded := kind.isLt
    omega

theorem event_certificate {α : Type} (table : List (Fin 5)) (index : Nat)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent table index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (sourceCondition observed = true) ∧
      branch (sourceCondition observed = true) normal first = branch (sourceCondition observed = true) normal second :=
  (explicit_panic (sourceCondition observed) normal first second).2
    (event_guard table index effects observed ran)
#print axioms event_guard
#print axioms event_certificate
end PV_B3P_KindEvents587227
