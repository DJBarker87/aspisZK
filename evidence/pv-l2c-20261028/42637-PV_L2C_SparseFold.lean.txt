import PV_L2C_QFold
set_option autoImplicit false
namespace PV_L2C_SparseFold
open PV_L2C_NativeQ PV_L2C_QBalance PV_L2C_QFold
/-- Literal native loop step: active rows skip field addition. -/
def run {I : Type} (active : I → Bool) (table : I → Q) : List I → Q → Q
 | [],s => s
 | i::is,s => run active table is (if active i then s else addQ s (table i))

theorem dense_projection {I : Type} (active : I → Bool) (table : I → Q)
    (rows : List I) (hc : ∀ i ∈ rows, Canonical (table i))
    (s : Q) (hs : Canonical s) :
    run active table rows s=
      foldQ (rows.map (fun i => if active i then zero else table i)) s := by
  induction rows generalizing s with
  | nil => rfl
  | cons i is ih =>
    have htail : ∀ i ∈ is, Canonical (table i) := fun i hi => hc i (by simp [hi])
    cases ha : active i with
    | false =>
      simp only [run,ha,Bool.false_eq_true,if_false,List.map_cons,foldQ]
      exact ih htail _ (add_canonical s (table i) hs (hc i (by simp)))
    | true =>
      simp only [run,ha,if_true,List.map_cons,foldQ,native_add_zero s hs]
      exact ih htail _ hs
#print axioms dense_projection

/-- ofFn id lists rows 0,...,n-1; there is no concrete 1024-cell reduction. -/
def sum {n : Nat} (active : Fin n → Bool) (table : Fin n → Q) : Q :=
  run active table (List.ofFn (fun i : Fin n => i)) zero

theorem source_sum {n : Nat} (active : Fin n → Bool) (table : Fin n → Q)
    (hc : ∀ i, Canonical (table i)) :
    sum active table=tableSum (inactiveTable active table) := by
  unfold sum
  rw [dense_projection active table _ (by
    intro i hi
    exact hc i) zero zero_canonical]
  simp only [List.map_ofFn,tableSum,inactiveTable,Function.comp_def]
#print axioms source_sum
end PV_L2C_SparseFold
