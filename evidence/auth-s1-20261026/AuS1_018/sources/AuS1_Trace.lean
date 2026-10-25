import AuS1_Association
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Trace
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode

def continueRun {A B : Type} (log : Log) (r : Result A) (k : A → Code B) : Log × Result B :=
  match r with
  | .ok a => let next := run (k a); (log ++ next.1,next.2)
  | .fail e => (log,.fail e)
  | .div => (log,.div)

/-- Ordered logs compose by append, preserving repeated calls and rejected prefixes. -/
theorem run_bind {A B : Type} (p : Code A) (k : A → Code B) :
    run (AspisR1PublicPreparation.PreparedHashCode.bind p k) = continueRun (run p).1 (run p).2 k := by
  induction p with
  | done a => simp only [AspisR1PublicPreparation.PreparedHashCode.bind,run,continueRun,List.nil_append]; rfl
  | step r next ih => cases r with
    | ok a => exact ih a
    | fail e => rfl
    | div => rfl
  | digest D hash parts next ih =>
    change run (AspisR1PublicPreparation.PreparedHashCode.bind (.digest D hash parts next) k) = _
    cases reply : D.digest hash parts with
    | fail e => simp only [AspisR1PublicPreparation.PreparedHashCode.bind,run,reply,continueRun]
    | div => simp only [AspisR1PublicPreparation.PreparedHashCode.bind,run,reply,continueRun]
    | ok a =>
      simp only [AspisR1PublicPreparation.PreparedHashCode.bind,run,reply,ih]
      cases h : (run (next a)).2 <;>
        simp only [continueRun,h,List.cons_append]

 theorem observe_append (a b : Log) : observe (a ++ b) = observe a ++ observe b :=
  List.flatMap_append

/-- Success of a composed source call exposes the SAME child result and
ordered child log, rather than selecting an independent accepting child. -/
theorem success_bind {A B : Type} (p : Code A) (k : A → Code B) (out : B)
    (success : erase (p >>= k) = ok out) :
    ∃ a, erase p = ok a ∧ erase (k a) = ok out ∧
      (run (p >>= k)).1 = (run p).1 ++ (run (k a)).1 := by
  rw [erase_bind] at success
  cases hp : erase p with
  | fail e => simp only [hp,bind_tc_fail] at success; cases success
  | div => simp only [hp,bind_tc_div] at success; cases success
  | ok a =>
    simp only [hp,bind_tc_ok] at success
    refine ⟨a,rfl,success,?_⟩
    rw [run_bind,run_value,hp]
    rfl

#print axioms run_bind
#print axioms observe_append
#print axioms success_bind
end AspisR1.AuS1_Trace
end
