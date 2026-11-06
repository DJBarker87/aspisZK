import NLK_BorrowScope
set_option autoImplicit false
namespace NLK_DriverFold
open Aeneas Aeneas.Std Result NLF_ParentModel
/-- Unlike a value-only Result, this carrier retains the last source prefix
when execution aborts. The SDK ledger is carried through every stage. -/
structure Outcome (E : Type) where
  parent : Parent
  result : Result (Except E Unit)

def thenRun {E : Type} (first : Outcome E) (next : Parent → Outcome E) : Outcome E :=
  match first.result with
  | .ok (.ok _) => next first.parent
  | .ok (.error e) => ⟨first.parent,.ok (.error e)⟩
  | .fail e => ⟨first.parent,.fail e⟩
  | .div => ⟨first.parent,.div⟩

def run {E C : Type} (step : Parent → C → Outcome E) (p : Parent) : List C → Outcome E
  | [] => ⟨p,.ok (.ok ())⟩
  | c::cs => thenRun (step p c) (fun q => run step q cs)

theorem then_assoc {E : Type} (r : Outcome E)
    (f g : Parent → Outcome E) :
    thenRun (thenRun r f) g = thenRun r (fun q => thenRun (f q) g) := by
  cases r with
  | mk p result => cases result with
    | ok reply => cases reply <;> rfl
    | fail e => rfl
    | div => rfl

/-- Local (bd) algebra. Concrete row roots must instantiate each source
occurrence and may not retain the arbitrary step parameter. -/
theorem source_order {E C : Type} (step : Parent → C → Outcome E)
    (p : Parent) (xs ys : List C) :
    run step p (xs++ys) = thenRun (run step p xs) (fun q => run step q ys) := by
  induction xs generalizing p with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append,run,ih,then_assoc]

theorem error_stops {E C : Type} (step : Parent → C → Outcome E)
    (p q : Parent) (c : C) (rest : List C) (e : E)
    (cut : step p c=⟨q,.ok (.error e)⟩) :
    run step p (c::rest)=⟨q,.ok (.error e)⟩ := by
  simp only [run,cut,thenRun]

theorem abort_stops {E C : Type} (step : Parent → C → Outcome E)
    (p q : Parent) (c : C) (rest : List C) (e : Error)
    (cut : step p c=⟨q,.fail e⟩) :
    run step p (c::rest)=⟨q,.fail e⟩ := by
  simp only [run,cut,thenRun]

theorem divergence_stops {E C : Type} (step : Parent → C → Outcome E)
    (p q : Parent) (c : C) (rest : List C)
    (cut : step p c=⟨q,.div⟩) : run step p (c::rest)=⟨q,.div⟩ := by
  simp only [run,cut,thenRun]

#print source_order
#print axioms then_assoc
#print axioms source_order
#print axioms error_stops
#print axioms abort_stops
#print axioms divergence_stops
end NLK_DriverFold
