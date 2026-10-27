import FJk_MaskValueStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_MaskValues
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
open FJk_MaskValueStep (model)
theorem m1024 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 1024#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [10] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 1024#u16 1023#u16 0#u16 10#u32 10#usize []
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>FJk_MaskValueStep.zero a s out hs r) run
#print axioms m1024
theorem m1536 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 1536#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [9, 10] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 1536#u16 1535#u16 1024#u16 9#u32 9#usize [10]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m1024 a ha s out hs r) run
#print axioms m1536
theorem m1664 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 1664#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [7, 9, 10] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 1664#u16 1663#u16 1536#u16 7#u32 7#usize [9, 10]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m1536 a ha s out hs r) run
#print axioms m1664
theorem m1728 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 1728#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [6, 7, 9, 10] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 1728#u16 1727#u16 1664#u16 6#u32 6#usize [7, 9, 10]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m1664 a ha s out hs r) run
#print axioms m1728
theorem m1744 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 1744#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [4, 6, 7, 9, 10] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 1744#u16 1743#u16 1728#u16 4#u32 4#usize [6, 7, 9, 10]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m1728 a ha s out hs r) run
#print axioms m1744
theorem m1748 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 1748#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [2, 4, 6, 7, 9, 10] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 1748#u16 1747#u16 1744#u16 2#u32 2#usize [4, 6, 7, 9, 10]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m1744 a ha s out hs r) run
#print axioms m1748
theorem m1749 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 1749#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [0, 2, 4, 6, 7, 9, 10] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 1749#u16 1748#u16 1748#u16 0#u32 0#usize [2, 4, 6, 7, 9, 10]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m1748 a ha s out hs r) run
#print axioms m1749
theorem m2048 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 2048#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [11] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 2048#u16 2047#u16 0#u16 11#u32 11#usize []
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>FJk_MaskValueStep.zero a s out hs r) run
#print axioms m2048
theorem m2049 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 2049#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [0, 11] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 2049#u16 2048#u16 2048#u16 0#u32 0#usize [11]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m2048 a ha s out hs r) run
#print axioms m2049
theorem m4096 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 4096#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [12] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 4096#u16 4095#u16 0#u16 12#u32 12#usize []
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>FJk_MaskValueStep.zero a s out hs r) run
#print axioms m4096
theorem m4097 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 4097#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [0, 12] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 4097#u16 4096#u16 4096#u16 0#u32 0#usize [12]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m4096 a ha s out hs r) run
#print axioms m4097
theorem m6144 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 6144#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [11, 12] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 6144#u16 6143#u16 4096#u16 11#u32 11#usize [12]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m4096 a ha s out hs r) run
#print axioms m6144
theorem m6145 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 6145#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [0, 11, 12] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 6145#u16 6144#u16 6144#u16 0#u32 0#usize [11, 12]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m6144 a ha s out hs r) run
#print axioms m6145
theorem m16384 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 16384#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [14] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 16384#u16 16383#u16 0#u16 14#u32 14#usize []
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>FJk_MaskValueStep.zero a s out hs r) run
#print axioms m16384
theorem m24576 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 24576#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [13, 14] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 24576#u16 24575#u16 16384#u16 13#u32 13#usize [14]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m16384 a ha s out hs r) run
#print axioms m24576
theorem m25600 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 25600#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [10, 13, 14] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 25600#u16 25599#u16 24576#u16 10#u32 10#usize [13, 14]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m24576 a ha s out hs r) run
#print axioms m25600
theorem m26112 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 26112#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [9, 10, 13, 14] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 26112#u16 26111#u16 25600#u16 9#u32 9#usize [10, 13, 14]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m25600 a ha s out hs r) run
#print axioms m26112
theorem m26176 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 26176#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [6, 9, 10, 13, 14] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 26176#u16 26175#u16 26112#u16 6#u32 6#usize [9, 10, 13, 14]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m26112 a ha s out hs r) run
#print axioms m26176
theorem m26208 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 26208#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [5, 6, 9, 10, 13, 14] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 26208#u16 26207#u16 26176#u16 5#u32 5#usize [6, 9, 10, 13, 14]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m26176 a ha s out hs r) run
#print axioms m26208
theorem m26212 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 26212#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [2, 5, 6, 9, 10, 13, 14] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 26212#u16 26211#u16 26208#u16 2#u32 2#usize [5, 6, 9, 10, 13, 14]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m26208 a ha s out hs r) run
#print axioms m26212
theorem m26214 (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a 26214#u16 false sum=ok out) :
    Canon out ∧ decode out=model a [1, 2, 5, 6, 9, 10, 13, 14] (decode sum) := by
  exact FJk_MaskValueStep.value a sum out 26214#u16 26213#u16 26212#u16 1#u32 1#usize [2, 5, 6, 9, 10, 13, 14]
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>m26212 a ha s out hs r) run
#print axioms m26214
theorem s6144 (a : Array field.QM31 16#usize) (ha : canonical a) (out : field.QM31)
    (run : selector_mask_sum_16 a 6144#u16=ok out) :
    Canon out ∧ decode out=model a [11, 12] 0 := by
  have factor : selector_mask_sum_16 a 6144#u16=selector_mask_sum_16_loop a 6144#u16 false field.QM31.ZERO := rfl
  rw [factor] at run
  simpa only [FIv_NativeValue.zero.2] using m6144 a ha field.QM31.ZERO out FIv_NativeValue.zero.1 run
#print axioms s6144
theorem s6145 (a : Array field.QM31 16#usize) (ha : canonical a) (out : field.QM31)
    (run : selector_mask_sum_16 a 6145#u16=ok out) :
    Canon out ∧ decode out=model a [0, 11, 12] 0 := by
  have factor : selector_mask_sum_16 a 6145#u16=selector_mask_sum_16_loop a 6145#u16 false field.QM31.ZERO := rfl
  rw [factor] at run
  simpa only [FIv_NativeValue.zero.2] using m6145 a ha field.QM31.ZERO out FIv_NativeValue.zero.1 run
#print axioms s6145
theorem s4097 (a : Array field.QM31 16#usize) (ha : canonical a) (out : field.QM31)
    (run : selector_mask_sum_16 a 4097#u16=ok out) :
    Canon out ∧ decode out=model a [0, 12] 0 := by
  have factor : selector_mask_sum_16 a 4097#u16=selector_mask_sum_16_loop a 4097#u16 false field.QM31.ZERO := rfl
  rw [factor] at run
  simpa only [FIv_NativeValue.zero.2] using m4097 a ha field.QM31.ZERO out FIv_NativeValue.zero.1 run
#print axioms s4097
theorem s2048 (a : Array field.QM31 16#usize) (ha : canonical a) (out : field.QM31)
    (run : selector_mask_sum_16 a 2048#u16=ok out) :
    Canon out ∧ decode out=model a [11] 0 := by
  have factor : selector_mask_sum_16 a 2048#u16=selector_mask_sum_16_loop a 2048#u16 false field.QM31.ZERO := rfl
  rw [factor] at run
  simpa only [FIv_NativeValue.zero.2] using m2048 a ha field.QM31.ZERO out FIv_NativeValue.zero.1 run
#print axioms s2048
theorem s2049 (a : Array field.QM31 16#usize) (ha : canonical a) (out : field.QM31)
    (run : selector_mask_sum_16 a 2049#u16=ok out) :
    Canon out ∧ decode out=model a [0, 11] 0 := by
  have factor : selector_mask_sum_16 a 2049#u16=selector_mask_sum_16_loop a 2049#u16 false field.QM31.ZERO := rfl
  rw [factor] at run
  simpa only [FIv_NativeValue.zero.2] using m2049 a ha field.QM31.ZERO out FIv_NativeValue.zero.1 run
#print axioms s2049
theorem s1749 (a : Array field.QM31 16#usize) (ha : canonical a) (out : field.QM31)
    (run : selector_mask_sum_16 a 1749#u16=ok out) :
    Canon out ∧ decode out=model a [0, 2, 4, 6, 7, 9, 10] 0 := by
  have factor : selector_mask_sum_16 a 1749#u16=selector_mask_sum_16_loop a 1749#u16 false field.QM31.ZERO := rfl
  rw [factor] at run
  simpa only [FIv_NativeValue.zero.2] using m1749 a ha field.QM31.ZERO out FIv_NativeValue.zero.1 run
#print axioms s1749
theorem s26214 (a : Array field.QM31 16#usize) (ha : canonical a) (out : field.QM31)
    (run : selector_mask_sum_16 a 26214#u16=ok out) :
    Canon out ∧ decode out=model a [1, 2, 5, 6, 9, 10, 13, 14] 0 := by
  have factor : selector_mask_sum_16 a 26214#u16=selector_mask_sum_16_loop a 26214#u16 false field.QM31.ZERO := rfl
  rw [factor] at run
  simpa only [FIv_NativeValue.zero.2] using m26214 a ha field.QM31.ZERO out FIv_NativeValue.zero.1 run
#print axioms s26214
end AspisR1.FJk_MaskValues
end
