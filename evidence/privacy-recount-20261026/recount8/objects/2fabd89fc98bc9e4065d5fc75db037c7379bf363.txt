import PV_B3P_ByteLayout226V3
import PV_B3P_LayoutIndex226
namespace PV_B3P_LayoutRegions226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false
attribute [local irreducible] fields PV_B3P_ByteLayout226V3.frontier indexBytes
set_option backward.isDefEq.respectTransparency false in
theorem variant (p : reference226.OwnedPublic) (i : Nat)
    (lo : 0 ≤ i) (hi : i < 1) :
    (layout p)[i]? = ([if p.withdrawal then 1#u8 else 0#u8])[i-0]? := by
  have h8 : (8#usize).val = 8 := rfl
  cases hw : p.withdrawal with
  | false =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = [] ++ ([0#u8]) ++ ((fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment [] ([0#u8]) ((fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 0
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
  | true =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = [] ++ ([1#u8]) ++ ((fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment [] ([1#u8]) ((fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 0
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
#print axioms variant
set_option backward.isDefEq.respectTransparency false in
theorem recipient_flag (p : reference226.OwnedPublic) (i : Nat)
    (lo : 69 ≤ i) (hi : i < 70) :
    (layout p)[i]? = ([if p.withdrawal then 0#u8 else 1#u8])[i-69]? := by
  have h8 : (8#usize).val = 8 := rfl
  cases hw : p.withdrawal with
  | false =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id])) ++ ([1#u8]) ++ ((fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id])) ([1#u8]) ((fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 69
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
  | true =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id])) ++ ([0#u8]) ++ ((fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id])) ([0#u8]) ((fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 69
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
#print axioms recipient_flag
set_option backward.isDefEq.respectTransparency false in
theorem withdrawal_flag (p : reference226.OwnedPublic) (i : Nat)
    (lo : (if p.withdrawal then 102 else 134) ≤ i) (hi : i < (if p.withdrawal then 103 else 135)) :
    (layout p)[i]? = ([if p.withdrawal then 1#u8 else 0#u8])[i-(if p.withdrawal then 102 else 134)]? := by
  have h8 : (8#usize).val = 8 := rfl
  cases hw : p.withdrawal with
  | false =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val)) ++ ([0#u8]) ++ ((indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val)) ([0#u8]) ((indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 134
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
  | true =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val)) ++ ([1#u8]) ++ ((fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val)) ([1#u8]) ((fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 102
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
#print axioms withdrawal_flag
set_option backward.isDefEq.respectTransparency false in
theorem anchor (p : reference226.OwnedPublic) (i : Nat)
    (lo : 1 ≤ i) (hi : i < 33) :
    (layout p)[i]? = (fields p.anchor.val)[i-1]? := by
  have h8 : (8#usize).val = 8 := rfl
  cases hw : p.withdrawal with
  | false =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([0#u8])) ++ (fields p.anchor.val) ++ ((fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([0#u8])) (fields p.anchor.val) ((fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 1
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
  | true =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([1#u8])) ++ (fields p.anchor.val) ++ ((fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([1#u8])) (fields p.anchor.val) ((fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 1
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
#print axioms anchor
set_option backward.isDefEq.respectTransparency false in
theorem nullifier (p : reference226.OwnedPublic) (i : Nat)
    (lo : 33 ≤ i) (hi : i < 65) :
    (layout p)[i]? = (fields p.nullifier.val)[i-33]? := by
  have h8 : (8#usize).val = 8 := rfl
  cases hw : p.withdrawal with
  | false =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([0#u8]) ++ (fields p.anchor.val)) ++ (fields p.nullifier.val) ++ ((fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([0#u8]) ++ (fields p.anchor.val)) (fields p.nullifier.val) ((fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 33
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
  | true =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([1#u8]) ++ (fields p.anchor.val)) ++ (fields p.nullifier.val) ++ ((fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([1#u8]) ++ (fields p.anchor.val)) (fields p.nullifier.val) ((fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 33
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
#print axioms nullifier
set_option backward.isDefEq.respectTransparency false in
theorem asset (p : reference226.OwnedPublic) (i : Nat)
    (lo : 65 ≤ i) (hi : i < 69) :
    (layout p)[i]? = (fields [p.asset_id])[i-65]? := by
  have h8 : (8#usize).val = 8 := rfl
  cases hw : p.withdrawal with
  | false =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val)) ++ (fields [p.asset_id]) ++ (([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val)) (fields [p.asset_id]) (([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 65
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
  | true =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val)) ++ (fields [p.asset_id]) ++ (([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val)) (fields [p.asset_id]) (([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 65
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
#print axioms asset
set_option backward.isDefEq.respectTransparency false in
theorem recipient (p : reference226.OwnedPublic) (i : Nat)
    (hw : p.withdrawal = false)
    (lo : 70 ≤ i) (hi : i < 102) :
    (layout p)[i]? = (fields p.recipient.val)[i-70]? := by
  have h8 : (8#usize).val = 8 := rfl
  try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
  have he : layout p = (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8])) ++ (fields p.recipient.val) ++ ((fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
    simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
  rw [he]
  apply PV_B3P_LayoutIndex226.at_segment (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8])) (fields p.recipient.val) ((fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 70
  · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
  · exact lo
  · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    omega
#print axioms recipient
set_option backward.isDefEq.respectTransparency false in
theorem change (p : reference226.OwnedPublic) (i : Nat)
    (lo : (if p.withdrawal then 70 else 102) ≤ i) (hi : i < (if p.withdrawal then 102 else 134)) :
    (layout p)[i]? = (fields p.change.val)[i-(if p.withdrawal then 70 else 102)]? := by
  have h8 : (8#usize).val = 8 := rfl
  cases hw : p.withdrawal with
  | false =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val)) ++ (fields p.change.val) ++ (([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val)) (fields p.change.val) (([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 102
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
  | true =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8])) ++ (fields p.change.val) ++ (([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8])) (fields p.change.val) (([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 70
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
#print axioms change
set_option backward.isDefEq.respectTransparency false in
theorem amount (p : reference226.OwnedPublic) (i : Nat)
    (hw : p.withdrawal = true)
    (lo : 103 ≤ i) (hi : i < 107) :
    (layout p)[i]? = (fields [p.withdrawal_amount])[i-103]? := by
  have h8 : (8#usize).val = 8 := rfl
  try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
  have he : layout p = (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8])) ++ (fields [p.withdrawal_amount]) ++ ((indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
    simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
  rw [he]
  apply PV_B3P_LayoutIndex226.at_segment (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8])) (fields [p.withdrawal_amount]) ((indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 103
  · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
  · exact lo
  · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    omega
#print axioms amount
set_option backward.isDefEq.respectTransparency false in
theorem index (p : reference226.OwnedPublic) (i : Nat)
    (lo : (if p.withdrawal then 107 else 135) ≤ i) (hi : i < (if p.withdrawal then 115 else 143)) :
    (layout p)[i]? = (indexBytes p.next_pair_index)[i-(if p.withdrawal then 107 else 135)]? := by
  have h8 : (8#usize).val = 8 := rfl
  cases hw : p.withdrawal with
  | false =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8])) ++ (indexBytes p.next_pair_index) ++ ((fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8])) (indexBytes p.next_pair_index) ((fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 135
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
  | true =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount])) ++ (indexBytes p.next_pair_index) ++ ((fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount])) (indexBytes p.next_pair_index) ((fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 107
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
#print axioms index
set_option backward.isDefEq.respectTransparency false in
theorem frontier (p : reference226.OwnedPublic) (i : Nat)
    (lo : (if p.withdrawal then 115 else 143) ≤ i) (hi : i < (if p.withdrawal then 755 else 783)) :
    (layout p)[i]? = (fields (PV_B3P_ByteLayout226V3.frontier p.frontier))[i-(if p.withdrawal then 115 else 143)]? := by
  have h8 : (8#usize).val = 8 := rfl
  cases hw : p.withdrawal with
  | false =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index)) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ ((fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index)) (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ((fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 143
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
  | true =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index)) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ ((fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index)) (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ((fields p.next_root.val) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 115
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
#print axioms frontier
set_option backward.isDefEq.respectTransparency false in
theorem next_root (p : reference226.OwnedPublic) (i : Nat)
    (lo : (if p.withdrawal then 755 else 783) ≤ i) (hi : i < (if p.withdrawal then 787 else 815)) :
    (layout p)[i]? = (fields p.next_root.val)[i-(if p.withdrawal then 755 else 783)]? := by
  have h8 : (8#usize).val = 8 := rfl
  cases hw : p.withdrawal with
  | false =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier))) ++ (fields p.next_root.val) ++ ((fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier))) (fields p.next_root.val) ((fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 783
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
  | true =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier))) ++ (fields p.next_root.val) ++ ((fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier))) (fields p.next_root.val) ((fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))) i 755
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
#print axioms next_root
set_option backward.isDefEq.respectTransparency false in
theorem next_frontier (p : reference226.OwnedPublic) (i : Nat)
    (lo : (if p.withdrawal then 787 else 815) ≤ i) (hi : i < (if p.withdrawal then 1427 else 1455)) :
    (layout p)[i]? = (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))[i-(if p.withdrawal then 787 else 815)]? := by
  have h8 : (8#usize).val = 8 := rfl
  cases hw : p.withdrawal with
  | false =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val)) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier)) ++ [] := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([0#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([1#u8]) ++ (fields p.recipient.val) ++ (fields p.change.val) ++ ([0#u8]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val)) (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier)) [] i 815
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
  | true =>
    try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have he : layout p = (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val)) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier)) ++ [] := by
      simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]
    rw [he]
    apply PV_B3P_LayoutIndex226.at_segment (([1#u8]) ++ (fields p.anchor.val) ++ (fields p.nullifier.val) ++ (fields [p.asset_id]) ++ ([0#u8]) ++ (fields p.change.val) ++ ([1#u8]) ++ (fields [p.withdrawal_amount]) ++ (indexBytes p.next_pair_index) ++ (fields (PV_B3P_ByteLayout226V3.frontier p.frontier)) ++ (fields p.next_root.val)) (fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier)) [] i 787
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
    · exact lo
    · simp only [fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8]
      omega
#print axioms next_frontier
end PV_B3P_LayoutRegions226
