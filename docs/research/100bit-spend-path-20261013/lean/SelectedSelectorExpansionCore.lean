import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/- Pure source-selector recurrence, reduced from SelectedSelectorExpansion.lean
   without its PositivePackBinding import cone. Declarations retain the same
   names and bodies for direct reuse. -/
set_option autoImplicit false
namespace AspisV8.SelectedSelectorExpansion
open scoped BigOperators

variable {K : Type*} [CommRing K]

def writePair (w : Nat → K) (x : K) (i j : Nat) : K :=
  if j=2*i then w i-x*w i else if j=2*i+1 then x*w i else w j

def sourceStores (w : Nat → K) (x : K) (i : Nat) : Nat → K :=
  let parent:=w i
  let right:=x*parent
  Function.update (Function.update w (2*i) (parent-right)) (2*i+1) right

theorem sourceStores_eq (w : Nat → K) (x : K) (i : Nat) :
    sourceStores w x i=writePair w x i := by
  funext j
  by_cases h0 : j=2*i
  · subst j
    simp [sourceStores,writePair]
  · by_cases h1 : j=2*i+1
    · subst j
      simp [sourceStores,writePair]
    · simp [sourceStores,writePair,h0,h1]

theorem writePair_below (w : Nat → K) (x : K) (i j : Nat) (h : j < i) :
    writePair w x i j=w j := by
  have h0 : j≠2*i := by omega
  have h1 : j≠2*i+1 := by omega
  simp only [writePair,h0,h1,if_false]

def descendingPass (x : K) : Nat → (Nat → K) → (Nat → K)
  | 0,w=>w
  | m+1,w=>descendingPass x m (writePair w x m)

def sourcePass (x : K) : Nat → (Nat → K) → (Nat → K)
  | 0,w=>w
  | m+1,w=>sourcePass x m (sourceStores w x m)

theorem sourcePass_eq (x : K) (m : Nat) (w : Nat → K) :
    sourcePass x m w=descendingPass x m w := by
  induction m generalizing w with
  | zero => rfl
  | succ m ih => rw [sourcePass,descendingPass,sourceStores_eq,ih]

theorem descendingPass_above (x : K) (m : Nat) (w : Nat → K)
    (j : Nat) (h : 2*m≤j) : descendingPass x m w j=w j := by
  induction m generalizing w with
  | zero => rfl
  | succ m ih =>
    rw [descendingPass,ih _ (by omega)]
    have h0 : j≠2*m := by omega
    have h1 : j≠2*m+1 := by omega
    simp only [writePair,h0,h1,if_false]

def factor (x : K) (b : Bool) : K := if b then x else 1-x

theorem descendingPass_lookup (x : K) (m : Nat) (w : Nat → K)
    (j : Nat) (h : j<2*m) :
    descendingPass x m w j=w (j/2)*factor x (j.testBit 0) := by
  induction m generalizing w j with
  | zero => omega
  | succ m ih =>
    by_cases low : j<2*m
    · have hp : j/2 < m := by omega
      rw [descendingPass,ih _ _ low,writePair_below w x m (j/2) hp]
    · have branches : j=2*m ∨ j=2*m+1 := by omega
      rcases branches with hzero|hone
      · subst j
        change descendingPass x m (writePair w x m) (2*m) =
          w ((2*m)/2) * factor x ((2*m).testBit 0)
        rw [descendingPass_above _ _ _ _ (by omega)]
        simp [writePair,factor,Nat.testBit_zero]
        ring
      · subst j
        change descendingPass x m (writePair w x m) (2*m+1) =
          w ((2*m+1)/2) * factor x ((2*m+1).testBit 0)
        rw [descendingPass_above _ _ _ _ (by omega)]
        have hd : (2*m+1)/2=m := by omega
        simp [writePair,factor,Nat.testBit_zero,hd]
        ring

def expand (z : Nat → K) : Nat → (Nat → K)
  | 0=>fun row=>if row=0 then 1 else 0
  | n+1=>sourcePass (z n) (2^n) (expand z n)

def tensorProduct (z : Nat → K) (n row : Nat) : K :=
  ∏ i ∈ Finset.range n,factor (z i) (row.testBit (n-1-i))

theorem expand_product (z : Nat → K) (n row : Nat) (h : row<2^n) :
    expand z n row=tensorProduct z n row := by
  induction n generalizing row with
  | zero =>
    have hr : row=0 := by simpa using h
    subst row
    simp [expand,tensorProduct]
  | succ n ih =>
    have hb : row<2*(2^n) := by simpa [pow_succ,mul_comm] using h
    have hp : row/2<2^n := by omega
    rw [expand,sourcePass_eq,descendingPass_lookup _ _ _ _ hb,ih _ hp]
    unfold tensorProduct
    rw [Finset.prod_range_succ]
    simp only [Nat.add_sub_cancel,Nat.sub_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    rw [Nat.testBit_div_two]
    congr 2
    omega

theorem selected_index_arithmetic (row : Nat) :
    row >>> 4=row/16 ∧ row &&& 15=row%16 := by
  constructor
  · simp [Nat.shiftRight_eq_div_pow]
  · simpa using Nat.and_two_pow_sub_one_eq_mod row 4

def selectedSelector (z : Nat → K) (row : Nat) : K :=
  expand z 6 (row >>> 4)*expand (fun i=>z (6+i)) 4 (row &&& 15)

theorem selected_selector_product (z : Nat → K) (row : Nat) (h : row<1024) :
    selectedSelector z row=tensorProduct z 10 row := by
  rcases selected_index_arithmetic row with ⟨hh,hl⟩
  unfold selectedSelector
  have hrow : row < 1024 := h
  have hhigh0 : row/16 < 64 := by omega
  have hlow0 : row%16 < 16 := Nat.mod_lt _ (by omega)
  have hhigh : row/16 < 2^6 := by
    simpa only [show (2^6 : Nat) = 64 by norm_num] using hhigh0
  have hlow : row%16 < 2^4 := by
    simpa only [show (2^4 : Nat) = 16 by norm_num] using hlow0
  rw [hh,hl,expand_product z 6 (row/16) hhigh,
    expand_product (fun i=>z (6+i)) 4 (row%16) hlow]
  change (∏ i ∈ Finset.range 6,factor (z i) ((row/16).testBit (5-i))) *
      (∏ i ∈ Finset.range 4,factor (z (6+i)) ((row%16).testBit (3-i)))=
    ∏ i ∈ Finset.range (6+4),factor (z i) (row.testBit (9-i))
  rw [Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    have hi' : i<6 := Finset.mem_range.mp hi
    have hb : (row/16).testBit (5-i)=row.testBit (9-i) := by
      rw [show (16 : Nat)=2^4 by decide,Nat.testBit_div_two_pow]
      congr 1
      omega
    rw [hb]
  · apply Finset.prod_congr rfl
    intro i hi
    have hi' : i<4 := Finset.mem_range.mp hi
    have hb : (row%16).testBit (3-i)=row.testBit (9-(6+i)) := by
      rw [show (16 : Nat)=2^4 by decide,Nat.testBit_mod_two_pow]
      have hj : 3-i<4 := by omega
      simp only [hj,decide_true,Bool.true_and]
      congr 1
      omega
    rw [hb]

#print axioms sourceStores_eq
#print axioms descendingPass_lookup
#print axioms expand_product
#print axioms selected_selector_product
end AspisV8.SelectedSelectorExpansion
