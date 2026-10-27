import XSa_DotRun
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSa_OptionFold

def absorb {A S : Type} (step : S → A → Result (Option S)) : Option S → A → Result (Option S)
 | none,_ => ok none
 | some s,a => step s a

def run {A S : Type} (step : S → A → Result (Option S)) : List A → S → Result (Option S)
 | [],s => ok (some s)
 | a::xs,s => do
   let next ← step s a
   match next with
   | none => ok none
   | some s' => run step xs s'

theorem none_fold {A S : Type} (step : S → A → Result (Option S)) (xs : List A) :
 xs.foldlM (absorb step) none=ok none := by
 induction xs with
 | nil => rfl
 | cons a xs ih => simpa only [List.foldlM_cons,absorb,bind_tc_ok] using ih

theorem same {A S : Type} (step : S → A → Result (Option S)) (xs : List A) (s : S) :
 run step xs s=xs.foldlM (absorb step) (some s) := by
 induction xs generalizing s with
 | nil => rfl
 | cons a xs ih =>
   simp only [run,List.foldlM_cons,absorb]
   apply (bind_eq_iff _ _ _).mpr
   intro next hnext
   cases next with
   | none => exact (none_fold step xs).symm
   | some s' => exact ih s'

#print axioms none_fold
#print axioms same
end XSa_OptionFold
