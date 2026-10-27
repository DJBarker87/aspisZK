import R1Z.PV_CB3_MonadicLoops
import Aeneas
set_option autoImplicit false
namespace R1Z.PV_CB3_ResultScan
open Aeneas Aeneas.Std Result

def scan {α : Type} (test : α → Result Bool) (clear : Bool) (xs : List α) : Result Bool :=
  xs.foldlM (fun acc x => do let b ← test x; ok (acc && b)) clear

theorem nil {α : Type} (test : α → Result Bool) (clear : Bool) :
    scan test clear [] = ok clear := rfl

theorem cons {α : Type} (test : α → Result Bool) (clear : Bool) (x : α) (xs : List α) :
    scan test clear (x::xs) = (do let b ← test x; scan test (clear && b) xs) := by
  simp only [scan,List.foldlM_cons,bind_assoc,bind_tc_ok]

theorem append {α : Type} (test : α → Result Bool) (clear : Bool) (xs ys : List α) :
    scan test clear (xs++ys) = (scan test clear xs >>= fun c => scan test c ys) := by
  exact PV_CB3_MonadicLoops.foldlM_append _ clear xs ys

theorem congr_test {α : Type} (f g : α → Result Bool)
    (agree : ∀ x, f x = g x) (clear : Bool) (xs : List α) :
    scan f clear xs = scan g clear xs := by
  apply PV_CB3_MonadicLoops.foldlM_congr
  intro acc x
  rw [agree]

theorem failure_even_if_false {α : Type} (test : α → Result Bool) (x : α)
    (xs : List α) (e : Error) (h : test x = fail e) :
    scan test false (x::xs) = fail e := by
  rw [cons,h]
  rfl

theorem divergence_even_if_false {α : Type} (test : α → Result Bool) (x : α)
    (xs : List α) (h : test x = div) :
    scan test false (x::xs) = div := by
  rw [cons,h]
  rfl
#print axioms nil
#print axioms cons
#print axioms append
#print axioms congr_test
#print axioms failure_even_if_false
#print axioms divergence_even_if_false
end R1Z.PV_CB3_ResultScan
