import Std
set_option autoImplicit false
namespace R1Z.PV_Countdown
-- Instantiate A with a Result carrier and step with a bind to preserve all failures.
def run {A : Type} (step : Nat → A → A) : Nat → A → A
  | 0, acc => acc
  | n+1, acc => run step n (step n acc)

theorem zero {A : Type} (step : Nat → A → A) (acc : A) : run step 0 acc = acc := rfl

theorem successor {A : Type} (step : Nat → A → A) (n : Nat) (acc : A) :
    run step (n+1) acc = run step n (step n acc) := rfl

theorem ordered {A : Type} (step : Nat → A → A) (n : Nat) (acc : A) :
    run step n acc = ((List.range n).reverse.foldl (fun state i => step i state) acc) := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    simp only [run,List.range_succ,List.reverse_append,List.reverse_singleton,
      List.cons_append,List.nil_append,List.foldl_cons,ih]
#print axioms zero
#print axioms successor
#print axioms ordered
end R1Z.PV_Countdown
