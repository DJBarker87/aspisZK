import RPu_JGa_MaskStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_MaskLoops
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

theorem m1024 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 1024#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 1024#u16 1023#u16 0#u16 10#u32 10#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (fun s hs=>⟨s,JGa_MaskStep.zero a s,hs⟩)
#print axioms m1024

theorem m1536 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 1536#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 1536#u16 1535#u16 1024#u16 9#u32 9#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m1024 a ha)
#print axioms m1536

theorem m1664 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 1664#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 1664#u16 1663#u16 1536#u16 7#u32 7#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m1536 a ha)
#print axioms m1664

theorem m1728 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 1728#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 1728#u16 1727#u16 1664#u16 6#u32 6#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m1664 a ha)
#print axioms m1728

theorem m1744 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 1744#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 1744#u16 1743#u16 1728#u16 4#u32 4#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m1728 a ha)
#print axioms m1744

theorem m1748 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 1748#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 1748#u16 1747#u16 1744#u16 2#u32 2#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m1744 a ha)
#print axioms m1748

theorem m1749 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 1749#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 1749#u16 1748#u16 1748#u16 0#u32 0#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m1748 a ha)
#print axioms m1749

theorem m2048 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 2048#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 2048#u16 2047#u16 0#u16 11#u32 11#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (fun s hs=>⟨s,JGa_MaskStep.zero a s,hs⟩)
#print axioms m2048

theorem m2049 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 2049#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 2049#u16 2048#u16 2048#u16 0#u32 0#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m2048 a ha)
#print axioms m2049

theorem m4096 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 4096#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 4096#u16 4095#u16 0#u16 12#u32 12#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (fun s hs=>⟨s,JGa_MaskStep.zero a s,hs⟩)
#print axioms m4096

theorem m4097 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 4097#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 4097#u16 4096#u16 4096#u16 0#u32 0#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m4096 a ha)
#print axioms m4097

theorem m6144 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 6144#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 6144#u16 6143#u16 4096#u16 11#u32 11#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m4096 a ha)
#print axioms m6144

theorem m6145 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 6145#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 6145#u16 6144#u16 6144#u16 0#u32 0#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m6144 a ha)
#print axioms m6145

theorem m16384 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 16384#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 16384#u16 16383#u16 0#u16 14#u32 14#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (fun s hs=>⟨s,JGa_MaskStep.zero a s,hs⟩)
#print axioms m16384

theorem m24576 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 24576#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 24576#u16 24575#u16 16384#u16 13#u32 13#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m16384 a ha)
#print axioms m24576

theorem m25600 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 25600#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 25600#u16 25599#u16 24576#u16 10#u32 10#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m24576 a ha)
#print axioms m25600

theorem m26112 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 26112#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 26112#u16 26111#u16 25600#u16 9#u32 9#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m25600 a ha)
#print axioms m26112

theorem m26176 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 26176#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 26176#u16 26175#u16 26112#u16 6#u32 6#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m26112 a ha)
#print axioms m26176

theorem m26208 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 26208#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 26208#u16 26207#u16 26176#u16 5#u32 5#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m26176 a ha)
#print axioms m26208

theorem m26212 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 26212#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 26212#u16 26211#u16 26208#u16 2#u32 2#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m26208 a ha)
#print axioms m26212

theorem m26214 (a : Array field.QM31 16#usize) (ha : canonical a) (sum : field.QM31) (hs : Canon sum) :
    ∃ out,selector_mask_sum_16_loop a 26214#u16 false sum=ok out ∧ Canon out := by
  exact JGa_MaskStep.source a sum 26214#u16 26213#u16 26212#u16 1#u32 1#usize
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq; scalar_tac) rfl rfl (m26212 a ha)
#print axioms m26214

theorem s6144 (a : Array field.QM31 16#usize) (ha : canonical a) :
    ∃ out,selector_mask_sum_16 a 6144#u16=ok out ∧ Canon out := by
  have factor : selector_mask_sum_16 a 6144#u16=selector_mask_sum_16_loop a 6144#u16 false field.QM31.ZERO := rfl
  rw [factor]
  exact m6144 a ha field.QM31.ZERO FIv_NativeValue.zero.1
#print axioms s6144

theorem s6145 (a : Array field.QM31 16#usize) (ha : canonical a) :
    ∃ out,selector_mask_sum_16 a 6145#u16=ok out ∧ Canon out := by
  have factor : selector_mask_sum_16 a 6145#u16=selector_mask_sum_16_loop a 6145#u16 false field.QM31.ZERO := rfl
  rw [factor]
  exact m6145 a ha field.QM31.ZERO FIv_NativeValue.zero.1
#print axioms s6145

theorem s4097 (a : Array field.QM31 16#usize) (ha : canonical a) :
    ∃ out,selector_mask_sum_16 a 4097#u16=ok out ∧ Canon out := by
  have factor : selector_mask_sum_16 a 4097#u16=selector_mask_sum_16_loop a 4097#u16 false field.QM31.ZERO := rfl
  rw [factor]
  exact m4097 a ha field.QM31.ZERO FIv_NativeValue.zero.1
#print axioms s4097

theorem s2048 (a : Array field.QM31 16#usize) (ha : canonical a) :
    ∃ out,selector_mask_sum_16 a 2048#u16=ok out ∧ Canon out := by
  have factor : selector_mask_sum_16 a 2048#u16=selector_mask_sum_16_loop a 2048#u16 false field.QM31.ZERO := rfl
  rw [factor]
  exact m2048 a ha field.QM31.ZERO FIv_NativeValue.zero.1
#print axioms s2048

theorem s2049 (a : Array field.QM31 16#usize) (ha : canonical a) :
    ∃ out,selector_mask_sum_16 a 2049#u16=ok out ∧ Canon out := by
  have factor : selector_mask_sum_16 a 2049#u16=selector_mask_sum_16_loop a 2049#u16 false field.QM31.ZERO := rfl
  rw [factor]
  exact m2049 a ha field.QM31.ZERO FIv_NativeValue.zero.1
#print axioms s2049

theorem s1749 (a : Array field.QM31 16#usize) (ha : canonical a) :
    ∃ out,selector_mask_sum_16 a 1749#u16=ok out ∧ Canon out := by
  have factor : selector_mask_sum_16 a 1749#u16=selector_mask_sum_16_loop a 1749#u16 false field.QM31.ZERO := rfl
  rw [factor]
  exact m1749 a ha field.QM31.ZERO FIv_NativeValue.zero.1
#print axioms s1749

theorem s26214 (a : Array field.QM31 16#usize) (ha : canonical a) :
    ∃ out,selector_mask_sum_16 a 26214#u16=ok out ∧ Canon out := by
  have factor : selector_mask_sum_16 a 26214#u16=selector_mask_sum_16_loop a 26214#u16 false field.QM31.ZERO := rfl
  rw [factor]
  exact m26214 a ha field.QM31.ZERO FIv_NativeValue.zero.1
#print axioms s26214
end AspisR1.JGa_MaskLoops
end
