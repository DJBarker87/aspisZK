import R1Z.PV_RunJoin_WeightResult46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightReadFold47
open Aeneas Aeneas.Std Result

theorem map_read {A B C I : Type} (raw : I → Result B)
    (mul : A → B → Result C) (add : C → C → Result C)
    (xs : List (A × I)) (ys : List (A × B))
    (h : List.Forall₂ (fun x y => x.1=y.1 ∧ raw x.2=ok y.2) xs ys) (sum : C) :
    xs.foldlM (fun acc term => do let b ← raw term.2; let p ← mul term.1 b; add acc p) sum =
      ys.foldlM (fun acc term => do let p ← mul term.1 term.2; add acc p) sum := by
  induction h generalizing sum with
  | nil => rfl
  | cons hxy htail ih =>
    rcases hxy with ⟨ha,hb⟩
    simp only [List.foldlM_cons,hb,ha,bind_tc_ok,bind_assoc,ih]
#print axioms map_read
end R1Z.PV_RunJoin_WeightReadFold47
