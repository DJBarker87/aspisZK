import Op5T_Marks
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_Control
open Aeneas Aeneas.Std Result
abbrev Site := S2LeadInterface.Site
/-- Result steps are literal source computations; marks are emitted at calls. -/
inductive Code (A : Type) : Type 1 where
  | done : A → Code A
  | step {B : Type} : Result B → (B → Code A) → Code A
  | mark : Site → Code A → Code A

def bind {A B : Type} : Code A → (A → Code B) → Code B
  | .done a, k => k a
  | .step r c, k => .step r (fun b => bind (c b) k)
  | .mark s c, k => .mark s (bind c k)
instance : Monad Code where
  pure := Code.done
  bind := bind

def liftResult {A : Type} (r : Result A) : Code A := .step r .done
instance : MonadLift Result Code where
  monadLift := liftResult

def emit {A : Type} (s : Site) (r : Result A) : Code A := .mark s (liftResult r)

def run {A : Type} : Code A → List Site → Result A × List Site
  | .done a, log => (.ok a,log)
  | .step r k, log => match r with
    | .ok a => run (k a) log
    | .fail e => (.fail e,log)
    | .div => (.div,log)
  | .mark s c, log => run c (log ++ [s])

def erase {A : Type} : Code A → Result A
  | .done a => .ok a
  | .step r k => do let a ← r; erase (k a)
  | .mark _ c => erase c

theorem erasure {A : Type} (code : Code A) (log : List Site) :
    (run code log).1 = erase code := by
  induction code generalizing log with
  | done a => rfl
  | step r k ih => cases r <;> first | rfl | exact ih _ log
  | mark s c ih => exact ih (log ++ [s])

theorem erase_bind {A B : Type} (c : Code A) (k : A → Code B) :
    erase (c >>= k) = (erase c >>= fun a => erase (k a)) := by
  induction c with
  | done a => rfl
  | step r next ih => cases r <;> first | rfl | exact ih _
  | mark s c ih => exact ih

theorem erase_lift {A : Type} (r : Result A) : erase (liftResult r) = r := by
  cases r <;> rfl

theorem erase_emit {A : Type} (s : Site) (r : Result A) : erase (emit s r) = r :=
  erase_lift r

theorem prefix_preserved {A : Type} (code : Code A) (log : List Site) :
    ∃ suffix, (run code log).2 = log ++ suffix := by
  induction code generalizing log with
  | done a => exact ⟨[],(List.append_nil _).symm⟩
  | step r k ih => cases r <;> first | exact ⟨[],(List.append_nil _).symm⟩ | exact ih _ log
  | mark s c ih =>
    obtain ⟨suffix,same⟩ := ih (log ++ [s])
    exact ⟨s :: suffix,by simpa only [run,List.append_assoc,List.singleton_append] using same⟩

#print axioms erasure
#print axioms erase_bind
#print axioms erase_lift
#print axioms erase_emit
#print axioms prefix_preserved
end AspisR1.SdkD_Control
end
