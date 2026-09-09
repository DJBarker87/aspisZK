import PositivePackBinding

/-! Mathematical source-loop refinement for Selectors::expand. The array
is represented by its total read function, with only the source's bounded
read/write range used. Descending writes are proved correct before reducing
the coordinate recursion to a product. No concrete 1024-cell recurrence is
unfolded. Rust machine memory and PreparedQm31Multiplier translation remain
separate from this field-level imperative-loop model. -/
set_option autoImplicit false
namespace AspisV8.SelectedSelectorExpansion
open scoped BigOperators
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositiveTerminalInsertion
open AspisV8.PositivePackBinding

variable {K : Type*} [CommRing K]

/-- Read parent once, then write the source's left and right children. -/
def writePair (w : Nat → K) (x : K) (i j : Nat) : K :=
  if j=2*i then w i-x*w i else if j=2*i+1 then x*w i else w j

/-- Literal sequential store model, both right/left values computed from
the parent read before either write. -/
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

/-- Source `(0..len).rev()` with exact read-before-write semantics. -/
def descendingPass (x : K) : Nat → (Nat → K) → (Nat → K)
  | 0,w=>w
  | m+1,w=>descendingPass x m (writePair w x m)

/-- The literal descending source loop uses the two sequential stores. -/
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

/-- All outputs, not merely honest or nonzero coordinates. Parent reads
remain intact because larger indices are processed first. -/
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
      rcases branches with rfl|rfl
      · rw [descendingPass,descendingPass_above _ _ _ _ (by omega)]
        simp [writePair,factor,Nat.testBit_zero]
        ring
      · rw [descendingPass,descendingPass_above _ _ _ _ (by omega)]
        have hd : (2*m+1)/2=m := by omega
        simp [writePair,factor,Nat.testBit_zero,hd]
        ring

/-- Source zero initialisation, weight[0]=1, len=1, then every coordinate
in forward/MSB order. Unused entries are explicitly zero initially. -/
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

/-- Exact source index operations, not an assumed high/low row map. -/
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
  rw [hh,hl,expand_product z 6 (row/16) (by norm_num; omega),
    expand_product (fun i=>z (6+i)) 4 (row%16) (by norm_num; omega)]
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

def booleanPoint (row : Nat) (i : Nat) : K := boolValue (row.testBit (9-i))

/-- Closes the selector premise previously left in PositivePackBinding.
The product is derived from the descending mutable-array model above. -/
theorem selected_selector_boolean (target row : Nat) (ht : target<1024) :
    selectedSelector (booleanPoint (K:=K) row) target=rowSelector (K:=K) target row := by
  rw [selected_selector_product _ _ ht]
  unfold tensorProduct
  rw [Finset.prod_range]
  rfl

def expandedLastPack (row : Nat) (asset publicAsset r c inv : QM31Exact) : QM31Exact :=
  let s:=selectedSelector (booleanPoint (K:=QM31Exact) row)
  literalPack ![s 44*(asset-publicAsset),(s 508+s 460)*(asset-publicAsset),
    s 1014*(r*c*inv-1),0]

theorem expanded_last_pack_eq (row : Nat) (asset publicAsset r c inv : QM31Exact) :
    expandedLastPack row asset publicAsset r c inv=sourceLastPack row asset publicAsset r c inv := by
  dsimp only [expandedLastPack,sourceLastPack]
  rw [selected_selector_boolean 44 row (by decide),selected_selector_boolean 508 row (by decide),
    selected_selector_boolean 460 row (by decide),selected_selector_boolean 1014 row (by decide)]

theorem expanded_row1014_pack_binding (asset publicAsset r c inv : QM31Exact) :
    expandedLastPack 1014 asset publicAsset r c inv=0 ↔ r*c*inv=1 := by
  rw [expanded_last_pack_eq,row1014_pack_binding]

#print axioms sourceStores_eq
#print axioms sourcePass_eq
#print axioms writePair_below
#print axioms descendingPass_above
#print axioms descendingPass_lookup
#print axioms expand_product
#print axioms selected_index_arithmetic
#print axioms selected_selector_product
#print axioms selected_selector_boolean
#print axioms expanded_last_pack_eq
#print axioms expanded_row1014_pack_binding
end AspisV8.SelectedSelectorExpansion
