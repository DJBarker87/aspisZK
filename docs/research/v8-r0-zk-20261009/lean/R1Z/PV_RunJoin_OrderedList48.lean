import R1Z.PV_RunJoin_WeightResult46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_OrderedList48

def run {A : Type} (f : Nat → A) (start : Nat) : Nat → List A
  | 0 => []
  | n+1 => f start :: run f (start+1) n

theorem complete {A : Type} (f : Nat → A) (start n : Nat) :
    run f start n=List.ofFn (fun i : Fin n => f (start+i.val)) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [run,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    apply congrArg (List.cons (f start))
    apply congrArg List.ofFn
    funext i
    rw [show start+1+i.val=start+(i.val+1) from by omega]
#print axioms complete
end R1Z.PV_RunJoin_OrderedList48
