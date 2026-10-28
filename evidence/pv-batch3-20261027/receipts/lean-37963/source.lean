import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse04
namespace PV_B3_MaskSparse03
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link024 : Array.index_usize host_forest.MASK_LINKS 24#usize = ok (539#u16,556#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer024 : P024 539 = 0#u8 := by
  dsimp only [P024, P023, P022, P021, P020, P019, P018, P017, Function.update]
  dsimp only [P016, P015, P014, P013, P012, P011, P010, P009, Function.update]
  dsimp only [P008, P007, P006, P005, P004, P003, P002, P001, Function.update]
  dsimp only [P000, Function.update]
  rfl
theorem consumer024 : C024 556 = 0#u8 := by
  dsimp only [C024, C023, C022, C021, C020, C019, C018, C017, Function.update]
  dsimp only [C016, C015, C014, C013, C012, C011, C010, C009, Function.update]
  dsimp only [C008, C007, C006, C005, C004, C003, C002, C001, Function.update]
  dsimp only [C000, Function.update]
  rfl
theorem step024 : body s024 = ok (cont s025) := by
  unfold body s024 s025 P025 C025 M025
  have next : Usize.wrapping_add 24#usize 1#usize = 25#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 24#usize (by
      change 25 < Usize.size; simpa using UScalar.hSize (25#usize))
  simpa only [next, show (539#usize).val = 539 from rfl,
    show (556#usize).val = 556 from rfl] using step P024 C024 M024 24#usize 539#usize 556#usize 539#u16 556#u16 1#u8 1#u8
    (by decide) link024 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P024 539) = _; rw [producer024]; rfl) (by change host_forest.mask_endpoint_bump (C024 556) = _; rw [consumer024]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link025 : Array.index_usize host_forest.MASK_LINKS 25#usize = ok (539#u16,544#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer025 : P025 539 = 1#u8 := by
  dsimp only [P025, P024, P023, P022, P021, P020, P019, P018, Function.update]
  dsimp only [P017, P016, P015, P014, P013, P012, P011, P010, Function.update]
  dsimp only [P009, P008, P007, P006, P005, P004, P003, P002, Function.update]
  dsimp only [P001, P000, Function.update]
  rfl
theorem consumer025 : C025 544 = 0#u8 := by
  dsimp only [C025, C024, C023, C022, C021, C020, C019, C018, Function.update]
  dsimp only [C017, C016, C015, C014, C013, C012, C011, C010, Function.update]
  dsimp only [C009, C008, C007, C006, C005, C004, C003, C002, Function.update]
  dsimp only [C001, C000, Function.update]
  rfl
theorem step025 : body s025 = ok (cont s026) := by
  unfold body s025 s026 P026 C026 M026
  have next : Usize.wrapping_add 25#usize 1#usize = 26#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 25#usize (by
      change 26 < Usize.size; simpa using UScalar.hSize (26#usize))
  simpa only [next, show (539#usize).val = 539 from rfl,
    show (544#usize).val = 544 from rfl] using step P025 C025 M025 25#usize 539#usize 544#usize 539#u16 544#u16 2#u8 1#u8
    (by decide) link025 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P025 539) = _; rw [producer025]; rfl) (by change host_forest.mask_endpoint_bump (C025 544) = _; rw [consumer025]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link026 : Array.index_usize host_forest.MASK_LINKS 26#usize = ok (555#u16,572#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer026 : P026 555 = 0#u8 := by
  dsimp only [P026, P025, P024, P023, P022, P021, P020, P019, Function.update]
  dsimp only [P018, P017, P016, P015, P014, P013, P012, P011, Function.update]
  dsimp only [P010, P009, P008, P007, P006, P005, P004, P003, Function.update]
  dsimp only [P002, P001, P000, Function.update]
  rfl
theorem consumer026 : C026 572 = 0#u8 := by
  dsimp only [C026, C025, C024, C023, C022, C021, C020, C019, Function.update]
  dsimp only [C018, C017, C016, C015, C014, C013, C012, C011, Function.update]
  dsimp only [C010, C009, C008, C007, C006, C005, C004, C003, Function.update]
  dsimp only [C002, C001, C000, Function.update]
  rfl
theorem step026 : body s026 = ok (cont s027) := by
  unfold body s026 s027 P027 C027 M027
  have next : Usize.wrapping_add 26#usize 1#usize = 27#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 26#usize (by
      change 27 < Usize.size; simpa using UScalar.hSize (27#usize))
  simpa only [next, show (555#usize).val = 555 from rfl,
    show (572#usize).val = 572 from rfl] using step P026 C026 M026 26#usize 555#usize 572#usize 555#u16 572#u16 1#u8 1#u8
    (by decide) link026 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P026 555) = _; rw [producer026]; rfl) (by change host_forest.mask_endpoint_bump (C026 572) = _; rw [consumer026]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link027 : Array.index_usize host_forest.MASK_LINKS 27#usize = ok (555#u16,560#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer027 : P027 555 = 1#u8 := by
  dsimp only [P027, P026, P025, P024, P023, P022, P021, P020, Function.update]
  dsimp only [P019, P018, P017, P016, P015, P014, P013, P012, Function.update]
  dsimp only [P011, P010, P009, P008, P007, P006, P005, P004, Function.update]
  dsimp only [P003, P002, P001, P000, Function.update]
  rfl
theorem consumer027 : C027 560 = 0#u8 := by
  dsimp only [C027, C026, C025, C024, C023, C022, C021, C020, Function.update]
  dsimp only [C019, C018, C017, C016, C015, C014, C013, C012, Function.update]
  dsimp only [C011, C010, C009, C008, C007, C006, C005, C004, Function.update]
  dsimp only [C003, C002, C001, C000, Function.update]
  rfl
theorem step027 : body s027 = ok (cont s028) := by
  unfold body s027 s028 P028 C028 M028
  have next : Usize.wrapping_add 27#usize 1#usize = 28#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 27#usize (by
      change 28 < Usize.size; simpa using UScalar.hSize (28#usize))
  simpa only [next, show (555#usize).val = 555 from rfl,
    show (560#usize).val = 560 from rfl] using step P027 C027 M027 27#usize 555#usize 560#usize 555#u16 560#u16 2#u8 1#u8
    (by decide) link027 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P027 555) = _; rw [producer027]; rfl) (by change host_forest.mask_endpoint_bump (C027 560) = _; rw [consumer027]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link028 : Array.index_usize host_forest.MASK_LINKS 28#usize = ok (571#u16,588#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer028 : P028 571 = 0#u8 := by
  dsimp only [P028, P027, P026, P025, P024, P023, P022, P021, Function.update]
  dsimp only [P020, P019, P018, P017, P016, P015, P014, P013, Function.update]
  dsimp only [P012, P011, P010, P009, P008, P007, P006, P005, Function.update]
  dsimp only [P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer028 : C028 588 = 0#u8 := by
  dsimp only [C028, C027, C026, C025, C024, C023, C022, C021, Function.update]
  dsimp only [C020, C019, C018, C017, C016, C015, C014, C013, Function.update]
  dsimp only [C012, C011, C010, C009, C008, C007, C006, C005, Function.update]
  dsimp only [C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step028 : body s028 = ok (cont s029) := by
  unfold body s028 s029 P029 C029 M029
  have next : Usize.wrapping_add 28#usize 1#usize = 29#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 28#usize (by
      change 29 < Usize.size; simpa using UScalar.hSize (29#usize))
  simpa only [next, show (571#usize).val = 571 from rfl,
    show (588#usize).val = 588 from rfl] using step P028 C028 M028 28#usize 571#usize 588#usize 571#u16 588#u16 1#u8 1#u8
    (by decide) link028 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P028 571) = _; rw [producer028]; rfl) (by change host_forest.mask_endpoint_bump (C028 588) = _; rw [consumer028]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link029 : Array.index_usize host_forest.MASK_LINKS 29#usize = ok (571#u16,576#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer029 : P029 571 = 1#u8 := by
  dsimp only [P029, P028, P027, P026, P025, P024, P023, P022, Function.update]
  dsimp only [P021, P020, P019, P018, P017, P016, P015, P014, Function.update]
  dsimp only [P013, P012, P011, P010, P009, P008, P007, P006, Function.update]
  dsimp only [P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer029 : C029 576 = 0#u8 := by
  dsimp only [C029, C028, C027, C026, C025, C024, C023, C022, Function.update]
  dsimp only [C021, C020, C019, C018, C017, C016, C015, C014, Function.update]
  dsimp only [C013, C012, C011, C010, C009, C008, C007, C006, Function.update]
  dsimp only [C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step029 : body s029 = ok (cont s030) := by
  unfold body s029 s030 P030 C030 M030
  have next : Usize.wrapping_add 29#usize 1#usize = 30#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 29#usize (by
      change 30 < Usize.size; simpa using UScalar.hSize (30#usize))
  simpa only [next, show (571#usize).val = 571 from rfl,
    show (576#usize).val = 576 from rfl] using step P029 C029 M029 29#usize 571#usize 576#usize 571#u16 576#u16 2#u8 1#u8
    (by decide) link029 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P029 571) = _; rw [producer029]; rfl) (by change host_forest.mask_endpoint_bump (C029 576) = _; rw [consumer029]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link030 : Array.index_usize host_forest.MASK_LINKS 30#usize = ok (587#u16,604#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer030 : P030 587 = 0#u8 := by
  dsimp only [P030, P029, P028, P027, P026, P025, P024, P023, Function.update]
  dsimp only [P022, P021, P020, P019, P018, P017, P016, P015, Function.update]
  dsimp only [P014, P013, P012, P011, P010, P009, P008, P007, Function.update]
  dsimp only [P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer030 : C030 604 = 0#u8 := by
  dsimp only [C030, C029, C028, C027, C026, C025, C024, C023, Function.update]
  dsimp only [C022, C021, C020, C019, C018, C017, C016, C015, Function.update]
  dsimp only [C014, C013, C012, C011, C010, C009, C008, C007, Function.update]
  dsimp only [C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step030 : body s030 = ok (cont s031) := by
  unfold body s030 s031 P031 C031 M031
  have next : Usize.wrapping_add 30#usize 1#usize = 31#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 30#usize (by
      change 31 < Usize.size; simpa using UScalar.hSize (31#usize))
  simpa only [next, show (587#usize).val = 587 from rfl,
    show (604#usize).val = 604 from rfl] using step P030 C030 M030 30#usize 587#usize 604#usize 587#u16 604#u16 1#u8 1#u8
    (by decide) link030 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P030 587) = _; rw [producer030]; rfl) (by change host_forest.mask_endpoint_bump (C030 604) = _; rw [consumer030]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link031 : Array.index_usize host_forest.MASK_LINKS 31#usize = ok (587#u16,592#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer031 : P031 587 = 1#u8 := by
  dsimp only [P031, P030, P029, P028, P027, P026, P025, P024, Function.update]
  dsimp only [P023, P022, P021, P020, P019, P018, P017, P016, Function.update]
  dsimp only [P015, P014, P013, P012, P011, P010, P009, P008, Function.update]
  dsimp only [P007, P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer031 : C031 592 = 0#u8 := by
  dsimp only [C031, C030, C029, C028, C027, C026, C025, C024, Function.update]
  dsimp only [C023, C022, C021, C020, C019, C018, C017, C016, Function.update]
  dsimp only [C015, C014, C013, C012, C011, C010, C009, C008, Function.update]
  dsimp only [C007, C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step031 : body s031 = ok (cont s032) := by
  unfold body s031 s032 P032 C032 M032
  have next : Usize.wrapping_add 31#usize 1#usize = 32#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 31#usize (by
      change 32 < Usize.size; simpa using UScalar.hSize (32#usize))
  simpa only [next, show (587#usize).val = 587 from rfl,
    show (592#usize).val = 592 from rfl] using step P031 C031 M031 31#usize 587#usize 592#usize 587#u16 592#u16 2#u8 1#u8
    (by decide) link031 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P031 587) = _; rw [producer031]; rfl) (by change host_forest.mask_endpoint_bump (C031 592) = _; rw [consumer031]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s024 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step024).trans ((run_next _ _ step025).trans ((run_next _ _ step026).trans ((run_next _ _ step027).trans ((run_next _ _ step028).trans ((run_next _ _ step029).trans ((run_next _ _ step030).trans ((run_next _ _ step031).trans (PV_B3_MaskSparse04.suffix))))))))
#print axioms link024
#print axioms producer024
#print axioms consumer024
#print axioms step024
#print axioms link025
#print axioms producer025
#print axioms consumer025
#print axioms step025
#print axioms link026
#print axioms producer026
#print axioms consumer026
#print axioms step026
#print axioms link027
#print axioms producer027
#print axioms consumer027
#print axioms step027
#print axioms link028
#print axioms producer028
#print axioms consumer028
#print axioms step028
#print axioms link029
#print axioms producer029
#print axioms consumer029
#print axioms step029
#print axioms link030
#print axioms producer030
#print axioms consumer030
#print axioms step030
#print axioms link031
#print axioms producer031
#print axioms consumer031
#print axioms step031
#print axioms suffix
end PV_B3_MaskSparse03
