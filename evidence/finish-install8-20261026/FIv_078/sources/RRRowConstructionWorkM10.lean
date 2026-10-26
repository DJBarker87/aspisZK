import GSStoredRowsEnvelopeM10
import BinTypedCacheWork

/-! Row construction in its stored list representation. The tariff for a
Taylor summand depends on a public integer/degree cap D, not on field values.
It includes a conservative binary-tree binomial tariff, the natural cast,
field exponentiation and list indexing. No coefficient table is reduced. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RRRowConstructionWorkM10
open CompPoly Polynomial RRDenseCoeffVector RRVectorRowPolynomialBridge
open ExtractorWorkMonad
variable {K : Type} [Field K]

def termTariff (D : Nat) : Nat := 100*(2^(D+1)+D+1)^2

def taylor (D : Nat) (cs : List K) (a : K) (j : Nat) : K × Nat :=
  let body := fun (total : K) i =>
    (total+(if j ≤ i then (i.choose j : K)*coeffAt cs i*a^(i-j) else 0), termTariff D)
  let r := ExtractorWorkMonad.forLoop cs.length body 0
  (r.1,r.2+cs.length+1)

theorem fold_add_sum (xs : List Nat) (f : Nat → K) (s : K) :
    xs.foldl (fun total i => total+f i) s = s+(xs.map f).sum := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

theorem range_sum (n : Nat) (f : Nat → K) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem taylor_value (D : Nat) (cs : List K) (a : K) (j : Nat) :
    (taylor D cs a j).1 = taylorCoeffVector cs a j := by
  simp only [taylor, ExtractorWorkMonad.forLoop_value, fold_add_sum, zero_add,
    range_sum, taylorCoeffVector]

theorem taylor_work (D : Nat) (cs : List K) (a : K) (j : Nat) :
    (taylor D cs a j).2 ≤ cs.length*termTariff D+cs.length+1 := by
  have h := ExtractorWorkMonad.forLoop_bound cs.length (termTariff D)
    (fun (total : K) i =>
      (total+(if j ≤ i then (i.choose j : K)*coeffAt cs i*a^(i-j) else 0), termTariff D))
    (fun _ _ _ => Nat.le_refl _) 0
  exact Nat.add_le_add_right (Nat.add_le_add_right h _) _

def valueAt (D : Nat) (gs : List (List K)) (a : K) (M n j : Nat) : K × Nat :=
  if j ≤ n then if n-j ≤ M then
    let row := BinTypedCacheWork.lookup gs (n-j)
    let r := taylor D (row.1.getD []) a j
    (r.1,row.2+r.2+4)
  else (0,4) else (0,4)

theorem valueAt_value (D : Nat) (gs : List (List K)) (a : K) (M n j : Nat) :
    (valueAt D gs a M n j).1 = rowValue gs a M n j := by
  simp only [valueAt, rowValue, BinTypedCacheWork.lookup_value, taylor_value, vectorAt]
  split <;> (try split) <;> rfl

theorem valueAt_work (D : Nat) (gs : List (List K)) (a : K) (M n j : Nat)
    (hn : n ≤ D) (hw : ∀ row ∈ gs, row.length ≤ D) :
    (valueAt D gs a M n j).2 ≤ D*termTariff D+2*D+6 := by
  have hg := BinTypedCacheWork.lookup_work gs (n-j)
  have hl : ((BinTypedCacheWork.lookup gs (n-j)).1.getD []).length ≤ D := by
    rw [BinTypedCacheWork.lookup_value]
    cases he : gs[n-j]? with
    | none => exact Nat.zero_le _
    | some row =>
      exact hw row (List.mem_of_getElem? he)
  have ht := taylor_work D ((BinTypedCacheWork.lookup gs (n-j)).1.getD []) a j
  have hm := Nat.mul_le_mul_right (termTariff D) hl
  simp only [valueAt]
  split
  · split <;> dsimp only <;> omega
  · omega

def row (D : Nat) (gs : List (List K)) (a : K) (M n : Nat) : List K × Nat :=
  let r := (List.finRange (n+1)).map (fun j => valueAt D gs a M n j.val)
  (r.map Prod.fst,(r.map Prod.snd).sum+n+2)

theorem row_value (D : Nat) (gs : List (List K)) (a : K) (M n : Nat) :
    (row D gs a M n).1 = RRVectorRowPolynomialBridge.row gs a M n := by
  simp only [row, List.map_map, Function.comp_def, valueAt_value,
    RRVectorRowPolynomialBridge.row, List.ofFn_eq_map]

theorem row_work (D : Nat) (gs : List (List K)) (a : K) (M n : Nat)
    (hn : n ≤ D) (hw : ∀ r ∈ gs, r.length ≤ D) :
    (row D gs a M n).2 ≤ (D+1)*(D*termTariff D+2*D+6)+D+2 := by
  have h := RawExtractorCostLedger.sum_charge_le (List.finRange (n+1))
    (fun j => (valueAt D gs a M n j.val).2) (D+1)
    (D*termTariff D+2*D+6) (by simp; omega)
    (fun j _ => valueAt_work D gs a M n j.val hn hw)
  change _+n+2 ≤ _
  simp only [List.map_map, Function.comp_def] at *
  omega

#print axioms fold_add_sum
#print axioms range_sum
#print axioms taylor_value
#print axioms taylor_work
#print axioms valueAt_value
#print axioms valueAt_work
#print axioms row_value
#print axioms row_work
end AspisR1.RRRowConstructionWorkM10
end
