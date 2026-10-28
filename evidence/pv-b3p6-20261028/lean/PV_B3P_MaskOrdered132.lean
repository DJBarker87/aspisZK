import PV_B3P_MaskOuter132
import PV_B3P_MaskCapacity132
import PV_B3P_MaskFreeLaw132
namespace PV_B3P_MaskOrdered132
open Aeneas Aeneas.Std PV_B3P_132 PV_B3P_MaskScan132 PV_B3P_MaskCount132
set_option autoImplicit false

theorem rows_list (p : Nat → Nat → Bool) (c r n : Nat) :
    rows p c r n = ((List.range' r n).filter (fun r => p r c)).map (fun r => (r,c)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    simp only [rows,List.range'_succ,List.filter_cons]
    split <;> simp_all

theorem columns_list (p : Nat → Nat → Bool) (c n : Nat) :
    columns p c n = (List.range' c n).flatMap (fun c =>
      ((List.range 1024).filter (fun r => p r c)).map (fun r => (r,c))) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [columns,List.range'_succ,List.flatMap_cons,ih,rows_list,List.range_eq_range']

theorem model_eq : columns pick 0 16 = PV_B3P_MaskModel132.cells := by
  rw [columns_list]
  simp only [PV_B3P_MaskModel132.cells,List.range_eq_range',pick]

theorem complete_result : ∃ out : Array reference132.Cell 3803#usize,
    reference132.cells = .ok (out,3803#usize) ∧
    out.val.map PV_B3P_MaskPrefix132.decode = PV_B3P_MaskModel132.cells := by
  have hp : ∀ (r c : Usize), r.val < 1024 → c.val < 16 →
      reference132.free r c = .ok (pick r.val c.val) := by
    intro r c _ _
    exact PV_B3P_MaskFreeLaw132.free_eq r c
  let initial : Array reference132.Cell 3803#usize := Array.repeat 3803#usize ⟨0#u16,0#u8⟩
  obtain ⟨out,k,hloop,hcount,hvalue⟩ := PV_B3P_MaskOuter132.outer pick hp 16 initial 0#usize 0#usize
    (by simp) (by simpa only [PV_B3P_MaskCapacity132.full_count] using (show 0+3803 ≤ 3803 by omega))
  have hk : k = 3803#usize := by
    apply UScalar.val_eq_imp
    simpa only [PV_B3P_MaskCapacity132.full_count] using hcount
  refine ⟨out,?_,?_⟩
  · simpa only [reference132.cells,hk] using hloop
  · rw [hk] at hvalue
    have hlen : out.val.length = 3803 := out.property
    simpa only [PV_B3P_MaskPrefix132.written,show (3803#usize).val = 3803 from rfl,
      show (0#usize).val = 0 from rfl,List.take_of_length_le (by omega : out.val.length ≤ 3803),
      List.take_zero,List.map_nil,List.nil_append,model_eq] using hvalue

#print axioms rows_list
#print axioms columns_list
#print axioms model_eq
#print axioms complete_result
end PV_B3P_MaskOrdered132
