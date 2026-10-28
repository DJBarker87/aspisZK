import PV_B3P_ByteLayout226V3
namespace PV_B3P_LayoutRegions226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false
theorem anchor (p : reference226.OwnedPublic) (i : Nat)
    (lo : 1 ≤ i) (hi : i < 33) :
    (layout p)[i]? = (fields p.anchor.val)[i-1]? := by
  cases hw : p.withdrawal <;>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;>
    simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
  all_goals
    repeat first
      | rw [List.getElem?_append_right (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
      | rw [List.getElem?_append_left (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
    first
    | rfl
    | congr 1 <;> omega
#print axioms anchor
theorem nullifier (p : reference226.OwnedPublic) (i : Nat)
    (lo : 33 ≤ i) (hi : i < 65) :
    (layout p)[i]? = (fields p.nullifier.val)[i-33]? := by
  cases hw : p.withdrawal <;>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;>
    simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
  all_goals
    repeat first
      | rw [List.getElem?_append_right (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
      | rw [List.getElem?_append_left (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
    first
    | rfl
    | congr 1 <;> omega
#print axioms nullifier
theorem asset (p : reference226.OwnedPublic) (i : Nat)
    (lo : 65 ≤ i) (hi : i < 69) :
    (layout p)[i]? = (fields [p.asset_id])[i-65]? := by
  cases hw : p.withdrawal <;>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;>
    simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
  all_goals
    repeat first
      | rw [List.getElem?_append_right (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
      | rw [List.getElem?_append_left (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
    first
    | rfl
    | congr 1 <;> omega
#print axioms asset
theorem recipient (p : reference226.OwnedPublic) (i : Nat)
    (hw : p.withdrawal = false)
    (lo : 70 ≤ i) (hi : i < 102) :
    (layout p)[i]? = (fields p.recipient.val)[i-70]? := by
  simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
  repeat first
    | rw [List.getElem?_append_right (by
        simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
          List.length_cons,List.length_nil]
        scalar_tac)]
    | rw [List.getElem?_append_left (by
        simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
          List.length_cons,List.length_nil]
        scalar_tac)]
  first
  | rfl
  | congr 1 <;> omega
#print axioms recipient
theorem change (p : reference226.OwnedPublic) (i : Nat)
    (lo : (if p.withdrawal then 70 else 102) ≤ i) (hi : i < (if p.withdrawal then 102 else 134)) :
    (layout p)[i]? = (fields p.change.val)[i-(if p.withdrawal then 70 else 102)]? := by
  cases hw : p.withdrawal <;>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;>
    simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
  all_goals
    repeat first
      | rw [List.getElem?_append_right (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
      | rw [List.getElem?_append_left (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
    first
    | rfl
    | congr 1 <;> omega
#print axioms change
theorem amount (p : reference226.OwnedPublic) (i : Nat)
    (hw : p.withdrawal = true)
    (lo : 103 ≤ i) (hi : i < 107) :
    (layout p)[i]? = (fields [p.withdrawal_amount])[i-103]? := by
  simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
  repeat first
    | rw [List.getElem?_append_right (by
        simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
          List.length_cons,List.length_nil]
        scalar_tac)]
    | rw [List.getElem?_append_left (by
        simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
          List.length_cons,List.length_nil]
        scalar_tac)]
  first
  | rfl
  | congr 1 <;> omega
#print axioms amount
theorem index (p : reference226.OwnedPublic) (i : Nat)
    (lo : (if p.withdrawal then 107 else 135) ≤ i) (hi : i < (if p.withdrawal then 115 else 143)) :
    (layout p)[i]? = (indexBytes p.next_pair_index)[i-(if p.withdrawal then 107 else 135)]? := by
  cases hw : p.withdrawal <;>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;>
    simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
  all_goals
    repeat first
      | rw [List.getElem?_append_right (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
      | rw [List.getElem?_append_left (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
    first
    | rfl
    | congr 1 <;> omega
#print axioms index
theorem frontier (p : reference226.OwnedPublic) (i : Nat)
    (lo : (if p.withdrawal then 115 else 143) ≤ i) (hi : i < (if p.withdrawal then 755 else 783)) :
    (layout p)[i]? = (fields (frontier p.frontier))[i-(if p.withdrawal then 115 else 143)]? := by
  cases hw : p.withdrawal <;>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;>
    simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
  all_goals
    repeat first
      | rw [List.getElem?_append_right (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
      | rw [List.getElem?_append_left (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
    first
    | rfl
    | congr 1 <;> omega
#print axioms frontier
theorem next_root (p : reference226.OwnedPublic) (i : Nat)
    (lo : (if p.withdrawal then 755 else 783) ≤ i) (hi : i < (if p.withdrawal then 787 else 815)) :
    (layout p)[i]? = (fields p.next_root.val)[i-(if p.withdrawal then 755 else 783)]? := by
  cases hw : p.withdrawal <;>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;>
    simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
  all_goals
    repeat first
      | rw [List.getElem?_append_right (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
      | rw [List.getElem?_append_left (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
    first
    | rfl
    | congr 1 <;> omega
#print axioms next_root
theorem next_frontier (p : reference226.OwnedPublic) (i : Nat)
    (lo : (if p.withdrawal then 787 else 815) ≤ i) (hi : i < (if p.withdrawal then 1427 else 1455)) :
    (layout p)[i]? = (fields (frontier p.next_frontier))[i-(if p.withdrawal then 787 else 815)]? := by
  cases hw : p.withdrawal <;>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;>
    simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
  all_goals
    repeat first
      | rw [List.getElem?_append_right (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
      | rw [List.getElem?_append_left (by
          simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
            List.length_cons,List.length_nil]
          scalar_tac)]
    first
    | rfl
    | congr 1 <;> omega
#print axioms next_frontier
end PV_B3P_LayoutRegions226
