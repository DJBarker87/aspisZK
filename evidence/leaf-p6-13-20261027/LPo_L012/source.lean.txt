import LPo_B_LPa_Fold
set_option autoImplicit false
namespace LPo.BA

def build {A : Type} (f : Nat → A) : Nat → List A
  | 0 => []
  | n+1 => build f n ++ [f n]
theorem build_map {A : Type} (f : Nat → A) (n : Nat) :
    build f n = (List.range n).map f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [build, ih, List.range_succ, List.map_append,
      List.map_cons, List.map_nil]
theorem build_fold {A : Type} (f : Nat → A) (n : Nat) :
    build f n = (List.range n).foldl (fun xs i => xs ++ [f i]) [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [build, ih, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
#print axioms build_map
#print axioms build_fold
end LPo.BA
