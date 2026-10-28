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
    rw [columns,List.range'_succ,List.flatMap_cons,ih,rows_list]
    rw [List.range_eq_range']

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
  have hcap : (0#usize).val + (columns pick (0#usize).val 16).length ≤ 3803 := by
    change 0+(columns pick 0 16).length ≤ 3803
    rw [PV_B3P_MaskCapacity132.full_count]
    omega
  obtain ⟨out,k,hloop,hcount,hvalue⟩ := PV_B3P_MaskOuter132.outer pick hp 16 initial 0#usize 0#usize
    (by simp) hcap
  change k.val = 0+(columns pick 0 16).length at hcount
  change PV_B3P_MaskPrefix132.written out k.val = [] ++ columns pick 0 16 at hvalue
  have hk : k = 3803#usize := by
    apply UScalar.val_eq_imp
    rw [PV_B3P_MaskCapacity132.full_count] at hcount
    exact hcount
  refine ⟨out,?_,?_⟩
  · simpa only [reference132.cells,hk] using hloop
  · rw [hk] at hvalue
    have hlen : out.val.length = 3803 := out.property
    change (out.val.take 3803).map PV_B3P_MaskPrefix132.decode = [] ++ columns pick 0 16 at hvalue
    rw [List.take_of_length_le (by omega : out.val.length ≤ 3803),List.nil_append,model_eq] at hvalue
    exact hvalue


#print axioms rows_list
#print axioms columns_list
#print axioms model_eq
#print axioms complete_result
end PV_B3P_MaskOrdered132
