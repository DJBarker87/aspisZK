import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse05
namespace PV_B3_MaskSparse04
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link032 : Array.index_usize host_forest.MASK_LINKS 32#usize = ok (603#u16,620#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer032 : P032 603 = 0#u8 := by
  dsimp only [P032, P031, P030, P029, P028, P027, P026, P025, Function.update]
  dsimp only [P024, P023, P022, P021, P020, P019, P018, P017, Function.update]
  dsimp only [P016, P015, P014, P013, P012, P011, P010, P009, Function.update]
  dsimp only [P008, P007, P006, P005, P004, P003, P002, P001, Function.update]
  dsimp only [P000, Function.update]
  rfl
theorem consumer032 : C032 620 = 0#u8 := by
  dsimp only [C032, C031, C030, C029, C028, C027, C026, C025, Function.update]
  dsimp only [C024, C023, C022, C021, C020, C019, C018, C017, Function.update]
  dsimp only [C016, C015, C014, C013, C012, C011, C010, C009, Function.update]
  dsimp only [C008, C007, C006, C005, C004, C003, C002, C001, Function.update]
  dsimp only [C000, Function.update]
  rfl
theorem step032 : body s032 = ok (cont s033) := by
  unfold body s032 s033 P033 C033 M033
  have next : Usize.wrapping_add 32#usize 1#usize = 33#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 32#usize (by
      change 33 < Usize.size; simpa using UScalar.hSize (33#usize))
  simpa only [next, show (603#usize).val = 603 from rfl,
    show (620#usize).val = 620 from rfl] using step P032 C032 M032 32#usize 603#usize 620#usize 603#u16 620#u16 1#u8 1#u8
    (by decide) link032 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P032 603) = _; rw [producer032]; rfl) (by change host_forest.mask_endpoint_bump (C032 620) = _; rw [consumer032]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link033 : Array.index_usize host_forest.MASK_LINKS 33#usize = ok (603#u16,608#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer033 : P033 603 = 1#u8 := by
  dsimp only [P033, P032, P031, P030, P029, P028, P027, P026, Function.update]
  dsimp only [P025, P024, P023, P022, P021, P020, P019, P018, Function.update]
  dsimp only [P017, P016, P015, P014, P013, P012, P011, P010, Function.update]
  dsimp only [P009, P008, P007, P006, P005, P004, P003, P002, Function.update]
  dsimp only [P001, P000, Function.update]
  rfl
theorem consumer033 : C033 608 = 0#u8 := by
  dsimp only [C033, C032, C031, C030, C029, C028, C027, C026, Function.update]
  dsimp only [C025, C024, C023, C022, C021, C020, C019, C018, Function.update]
  dsimp only [C017, C016, C015, C014, C013, C012, C011, C010, Function.update]
  dsimp only [C009, C008, C007, C006, C005, C004, C003, C002, Function.update]
  dsimp only [C001, C000, Function.update]
  rfl
theorem step033 : body s033 = ok (cont s034) := by
  unfold body s033 s034 P034 C034 M034
  have next : Usize.wrapping_add 33#usize 1#usize = 34#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 33#usize (by
      change 34 < Usize.size; simpa using UScalar.hSize (34#usize))
  simpa only [next, show (603#usize).val = 603 from rfl,
    show (608#usize).val = 608 from rfl] using step P033 C033 M033 33#usize 603#usize 608#usize 603#u16 608#u16 2#u8 1#u8
    (by decide) link033 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P033 603) = _; rw [producer033]; rfl) (by change host_forest.mask_endpoint_bump (C033 608) = _; rw [consumer033]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link034 : Array.index_usize host_forest.MASK_LINKS 34#usize = ok (619#u16,636#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer034 : P034 619 = 0#u8 := by
  dsimp only [P034, P033, P032, P031, P030, P029, P028, P027, Function.update]
  dsimp only [P026, P025, P024, P023, P022, P021, P020, P019, Function.update]
  dsimp only [P018, P017, P016, P015, P014, P013, P012, P011, Function.update]
  dsimp only [P010, P009, P008, P007, P006, P005, P004, P003, Function.update]
  dsimp only [P002, P001, P000, Function.update]
  rfl
theorem consumer034 : C034 636 = 0#u8 := by
  dsimp only [C034, C033, C032, C031, C030, C029, C028, C027, Function.update]
  dsimp only [C026, C025, C024, C023, C022, C021, C020, C019, Function.update]
  dsimp only [C018, C017, C016, C015, C014, C013, C012, C011, Function.update]
  dsimp only [C010, C009, C008, C007, C006, C005, C004, C003, Function.update]
  dsimp only [C002, C001, C000, Function.update]
  rfl
theorem step034 : body s034 = ok (cont s035) := by
  unfold body s034 s035 P035 C035 M035
  have next : Usize.wrapping_add 34#usize 1#usize = 35#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 34#usize (by
      change 35 < Usize.size; simpa using UScalar.hSize (35#usize))
  simpa only [next, show (619#usize).val = 619 from rfl,
    show (636#usize).val = 636 from rfl] using step P034 C034 M034 34#usize 619#usize 636#usize 619#u16 636#u16 1#u8 1#u8
    (by decide) link034 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P034 619) = _; rw [producer034]; rfl) (by change host_forest.mask_endpoint_bump (C034 636) = _; rw [consumer034]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link035 : Array.index_usize host_forest.MASK_LINKS 35#usize = ok (619#u16,624#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer035 : P035 619 = 1#u8 := by
  dsimp only [P035, P034, P033, P032, P031, P030, P029, P028, Function.update]
  dsimp only [P027, P026, P025, P024, P023, P022, P021, P020, Function.update]
  dsimp only [P019, P018, P017, P016, P015, P014, P013, P012, Function.update]
  dsimp only [P011, P010, P009, P008, P007, P006, P005, P004, Function.update]
  dsimp only [P003, P002, P001, P000, Function.update]
  rfl
theorem consumer035 : C035 624 = 0#u8 := by
  dsimp only [C035, C034, C033, C032, C031, C030, C029, C028, Function.update]
  dsimp only [C027, C026, C025, C024, C023, C022, C021, C020, Function.update]
  dsimp only [C019, C018, C017, C016, C015, C014, C013, C012, Function.update]
  dsimp only [C011, C010, C009, C008, C007, C006, C005, C004, Function.update]
  dsimp only [C003, C002, C001, C000, Function.update]
  rfl
theorem step035 : body s035 = ok (cont s036) := by
  unfold body s035 s036 P036 C036 M036
  have next : Usize.wrapping_add 35#usize 1#usize = 36#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 35#usize (by
      change 36 < Usize.size; simpa using UScalar.hSize (36#usize))
  simpa only [next, show (619#usize).val = 619 from rfl,
    show (624#usize).val = 624 from rfl] using step P035 C035 M035 35#usize 619#usize 624#usize 619#u16 624#u16 2#u8 1#u8
    (by decide) link035 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P035 619) = _; rw [producer035]; rfl) (by change host_forest.mask_endpoint_bump (C035 624) = _; rw [consumer035]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link036 : Array.index_usize host_forest.MASK_LINKS 36#usize = ok (635#u16,652#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer036 : P036 635 = 0#u8 := by
  dsimp only [P036, P035, P034, P033, P032, P031, P030, P029, Function.update]
  dsimp only [P028, P027, P026, P025, P024, P023, P022, P021, Function.update]
  dsimp only [P020, P019, P018, P017, P016, P015, P014, P013, Function.update]
  dsimp only [P012, P011, P010, P009, P008, P007, P006, P005, Function.update]
  dsimp only [P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer036 : C036 652 = 0#u8 := by
  dsimp only [C036, C035, C034, C033, C032, C031, C030, C029, Function.update]
  dsimp only [C028, C027, C026, C025, C024, C023, C022, C021, Function.update]
  dsimp only [C020, C019, C018, C017, C016, C015, C014, C013, Function.update]
  dsimp only [C012, C011, C010, C009, C008, C007, C006, C005, Function.update]
  dsimp only [C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step036 : body s036 = ok (cont s037) := by
  unfold body s036 s037 P037 C037 M037
  have next : Usize.wrapping_add 36#usize 1#usize = 37#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 36#usize (by
      change 37 < Usize.size; simpa using UScalar.hSize (37#usize))
  simpa only [next, show (635#usize).val = 635 from rfl,
    show (652#usize).val = 652 from rfl] using step P036 C036 M036 36#usize 635#usize 652#usize 635#u16 652#u16 1#u8 1#u8
    (by decide) link036 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P036 635) = _; rw [producer036]; rfl) (by change host_forest.mask_endpoint_bump (C036 652) = _; rw [consumer036]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link037 : Array.index_usize host_forest.MASK_LINKS 37#usize = ok (635#u16,640#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer037 : P037 635 = 1#u8 := by
  dsimp only [P037, P036, P035, P034, P033, P032, P031, P030, Function.update]
  dsimp only [P029, P028, P027, P026, P025, P024, P023, P022, Function.update]
  dsimp only [P021, P020, P019, P018, P017, P016, P015, P014, Function.update]
  dsimp only [P013, P012, P011, P010, P009, P008, P007, P006, Function.update]
  dsimp only [P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer037 : C037 640 = 0#u8 := by
  dsimp only [C037, C036, C035, C034, C033, C032, C031, C030, Function.update]
  dsimp only [C029, C028, C027, C026, C025, C024, C023, C022, Function.update]
  dsimp only [C021, C020, C019, C018, C017, C016, C015, C014, Function.update]
  dsimp only [C013, C012, C011, C010, C009, C008, C007, C006, Function.update]
  dsimp only [C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step037 : body s037 = ok (cont s038) := by
  unfold body s037 s038 P038 C038 M038
  have next : Usize.wrapping_add 37#usize 1#usize = 38#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 37#usize (by
      change 38 < Usize.size; simpa using UScalar.hSize (38#usize))
  simpa only [next, show (635#usize).val = 635 from rfl,
    show (640#usize).val = 640 from rfl] using step P037 C037 M037 37#usize 635#usize 640#usize 635#u16 640#u16 2#u8 1#u8
    (by decide) link037 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P037 635) = _; rw [producer037]; rfl) (by change host_forest.mask_endpoint_bump (C037 640) = _; rw [consumer037]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link038 : Array.index_usize host_forest.MASK_LINKS 38#usize = ok (651#u16,668#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer038 : P038 651 = 0#u8 := by
  dsimp only [P038, P037, P036, P035, P034, P033, P032, P031, Function.update]
  dsimp only [P030, P029, P028, P027, P026, P025, P024, P023, Function.update]
  dsimp only [P022, P021, P020, P019, P018, P017, P016, P015, Function.update]
  dsimp only [P014, P013, P012, P011, P010, P009, P008, P007, Function.update]
  dsimp only [P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer038 : C038 668 = 0#u8 := by
  dsimp only [C038, C037, C036, C035, C034, C033, C032, C031, Function.update]
  dsimp only [C030, C029, C028, C027, C026, C025, C024, C023, Function.update]
  dsimp only [C022, C021, C020, C019, C018, C017, C016, C015, Function.update]
  dsimp only [C014, C013, C012, C011, C010, C009, C008, C007, Function.update]
  dsimp only [C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step038 : body s038 = ok (cont s039) := by
  unfold body s038 s039 P039 C039 M039
  have next : Usize.wrapping_add 38#usize 1#usize = 39#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 38#usize (by
      change 39 < Usize.size; simpa using UScalar.hSize (39#usize))
  simpa only [next, show (651#usize).val = 651 from rfl,
    show (668#usize).val = 668 from rfl] using step P038 C038 M038 38#usize 651#usize 668#usize 651#u16 668#u16 1#u8 1#u8
    (by decide) link038 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P038 651) = _; rw [producer038]; rfl) (by change host_forest.mask_endpoint_bump (C038 668) = _; rw [consumer038]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link039 : Array.index_usize host_forest.MASK_LINKS 39#usize = ok (651#u16,656#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer039 : P039 651 = 1#u8 := by
  dsimp only [P039, P038, P037, P036, P035, P034, P033, P032, Function.update]
  dsimp only [P031, P030, P029, P028, P027, P026, P025, P024, Function.update]
  dsimp only [P023, P022, P021, P020, P019, P018, P017, P016, Function.update]
  dsimp only [P015, P014, P013, P012, P011, P010, P009, P008, Function.update]
  dsimp only [P007, P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer039 : C039 656 = 0#u8 := by
  dsimp only [C039, C038, C037, C036, C035, C034, C033, C032, Function.update]
  dsimp only [C031, C030, C029, C028, C027, C026, C025, C024, Function.update]
  dsimp only [C023, C022, C021, C020, C019, C018, C017, C016, Function.update]
  dsimp only [C015, C014, C013, C012, C011, C010, C009, C008, Function.update]
  dsimp only [C007, C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step039 : body s039 = ok (cont s040) := by
  unfold body s039 s040 P040 C040 M040
  have next : Usize.wrapping_add 39#usize 1#usize = 40#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 39#usize (by
      change 40 < Usize.size; simpa using UScalar.hSize (40#usize))
  simpa only [next, show (651#usize).val = 651 from rfl,
    show (656#usize).val = 656 from rfl] using step P039 C039 M039 39#usize 651#usize 656#usize 651#u16 656#u16 2#u8 1#u8
    (by decide) link039 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P039 651) = _; rw [producer039]; rfl) (by change host_forest.mask_endpoint_bump (C039 656) = _; rw [consumer039]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s032 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step032).trans ((run_next _ _ step033).trans ((run_next _ _ step034).trans ((run_next _ _ step035).trans ((run_next _ _ step036).trans ((run_next _ _ step037).trans ((run_next _ _ step038).trans ((run_next _ _ step039).trans (PV_B3_MaskSparse05.suffix))))))))
#print axioms link032
#print axioms producer032
#print axioms consumer032
#print axioms step032
#print axioms link033
#print axioms producer033
#print axioms consumer033
#print axioms step033
#print axioms link034
#print axioms producer034
#print axioms consumer034
#print axioms step034
#print axioms link035
#print axioms producer035
#print axioms consumer035
#print axioms step035
#print axioms link036
#print axioms producer036
#print axioms consumer036
#print axioms step036
#print axioms link037
#print axioms producer037
#print axioms consumer037
#print axioms step037
#print axioms link038
#print axioms producer038
#print axioms consumer038
#print axioms step038
#print axioms link039
#print axioms producer039
#print axioms consumer039
#print axioms step039
#print axioms suffix
end PV_B3_MaskSparse04
