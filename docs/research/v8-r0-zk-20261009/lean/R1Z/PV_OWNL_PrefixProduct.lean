import R1Z.PV_OWNI_DensePrune
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNL_PrefixProduct
variable {K : Type} [Field K]
/-- The field step appearing in DecodeWeight, without changing its order. -/
def step (width pref : Nat) (acc : K × Nat) (coordinate : K) : K × Nat :=
 (acc.1 * (if pref.testBit (width-1-acc.2) then coordinate else 1-coordinate),acc.2+1)

def factors (width pref : Nat) : Nat → List K → List K
 | _,[] => []
 | index,x::xs =>
  (if pref.testBit (width-1-index) then x else 1-x) :: factors width pref (index+1) xs

theorem fold_product (width pref : Nat) (xs : List K) (acc : K) (index : Nat) :
 (xs.foldl (step width pref) (acc,index)).1 = acc * (factors width pref index xs).prod := by
 induction xs generalizing acc index with
 | nil => simp only [List.foldl_nil,factors,List.prod_nil,mul_one]
 | cons x xs ih =>
  simp only [List.foldl_cons,step]
  rw [ih]
  simp only [factors,List.prod_cons,mul_assoc]

open scoped BigOperators

theorem factors_product (width pref : Nat) (xs : List K) (index : Nat) :
 (factors width pref index xs).prod =
 ∏ i : Fin xs.length,
  if pref.testBit (width-1-(index+i.val)) then xs.get i else 1-xs.get i := by
 induction xs generalizing index with
 | nil => simp only [factors,List.prod_nil,List.length_nil,Fin.prod_univ_zero]
 | cons x xs ih =>
  simp only [factors,List.prod_cons,List.length_cons,Fin.prod_univ_succ,
   List.get_cons_zero,List.get_cons_succ',Fin.val_zero,Fin.val_succ,Nat.add_zero]
  rw [ih]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have h : index+1+i.val = index+(i.val+1) := by omega
  rw [h]

/-- Direct list fold to the usual Boolean-cube product; symbolic in width. -/
theorem prefix_weight (xs : List K) (pref : Fin (2^xs.length)) :
 (xs.foldl (step xs.length pref.val) (1,0)).1 =
 PV_OWNI_DensePrune.weight (fun i : Fin xs.length => xs.get i)
  (fun i => pref.val.testBit (xs.length-1-i.val)) := by
 rw [fold_product,factors_product,one_mul]
 simp only [PV_OWNI_DensePrune.weight,Nat.zero_add]
#print axioms fold_product
#print axioms factors_product
#print axioms prefix_weight
end R1Z.PV_OWNL_PrefixProduct
