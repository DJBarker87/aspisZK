import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse06
namespace PV_B3_MaskSparse05
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link040 : Array.index_usize host_forest.MASK_LINKS 40#usize = ok (667#u16,684#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer040 : P040 667 = 0#u8 := by
  dsimp only [P040, P039, P038, P037, P036, P035, P034, P033, Function.update]
  dsimp only [P032, P031, P030, P029, P028, P027, P026, P025, Function.update]
  dsimp only [P024, P023, P022, P021, P020, P019, P018, P017, Function.update]
  dsimp only [P016, P015, P014, P013, P012, P011, P010, P009, Function.update]
  dsimp only [P008, P007, P006, P005, P004, P003, P002, P001, Function.update]
  dsimp only [P000, Function.update]
  rfl
theorem consumer040 : C040 684 = 0#u8 := by
  dsimp only [C040, C039, C038, C037, C036, C035, C034, C033, Function.update]
  dsimp only [C032, C031, C030, C029, C028, C027, C026, C025, Function.update]
  dsimp only [C024, C023, C022, C021, C020, C019, C018, C017, Function.update]
  dsimp only [C016, C015, C014, C013, C012, C011, C010, C009, Function.update]
  dsimp only [C008, C007, C006, C005, C004, C003, C002, C001, Function.update]
  dsimp only [C000, Function.update]
  rfl
theorem step040 : body s040 = ok (cont s041) := by
  unfold body s040 s041 P041 C041 M041
  have next : Usize.wrapping_add 40#usize 1#usize = 41#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 40#usize (by
      change 41 < Usize.size; simpa using UScalar.hSize (41#usize))
  simpa only [next, show (667#usize).val = 667 from rfl,
    show (684#usize).val = 684 from rfl] using step P040 C040 M040 40#usize 667#usize 684#usize 667#u16 684#u16 1#u8 1#u8
    (by decide) link040 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P040 667) = _; rw [producer040]; rfl) (by change host_forest.mask_endpoint_bump (C040 684) = _; rw [consumer040]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link041 : Array.index_usize host_forest.MASK_LINKS 41#usize = ok (667#u16,672#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer041 : P041 667 = 1#u8 := by
  dsimp only [P041, P040, P039, P038, P037, P036, P035, P034, Function.update]
  dsimp only [P033, P032, P031, P030, P029, P028, P027, P026, Function.update]
  dsimp only [P025, P024, P023, P022, P021, P020, P019, P018, Function.update]
  dsimp only [P017, P016, P015, P014, P013, P012, P011, P010, Function.update]
  dsimp only [P009, P008, P007, P006, P005, P004, P003, P002, Function.update]
  dsimp only [P001, P000, Function.update]
  rfl
theorem consumer041 : C041 672 = 0#u8 := by
  dsimp only [C041, C040, C039, C038, C037, C036, C035, C034, Function.update]
  dsimp only [C033, C032, C031, C030, C029, C028, C027, C026, Function.update]
  dsimp only [C025, C024, C023, C022, C021, C020, C019, C018, Function.update]
  dsimp only [C017, C016, C015, C014, C013, C012, C011, C010, Function.update]
  dsimp only [C009, C008, C007, C006, C005, C004, C003, C002, Function.update]
  dsimp only [C001, C000, Function.update]
  rfl
theorem step041 : body s041 = ok (cont s042) := by
  unfold body s041 s042 P042 C042 M042
  have next : Usize.wrapping_add 41#usize 1#usize = 42#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 41#usize (by
      change 42 < Usize.size; simpa using UScalar.hSize (42#usize))
  simpa only [next, show (667#usize).val = 667 from rfl,
    show (672#usize).val = 672 from rfl] using step P041 C041 M041 41#usize 667#usize 672#usize 667#u16 672#u16 2#u8 1#u8
    (by decide) link041 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P041 667) = _; rw [producer041]; rfl) (by change host_forest.mask_endpoint_bump (C041 672) = _; rw [consumer041]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link042 : Array.index_usize host_forest.MASK_LINKS 42#usize = ok (683#u16,700#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer042 : P042 683 = 0#u8 := by
  dsimp only [P042, P041, P040, P039, P038, P037, P036, P035, Function.update]
  dsimp only [P034, P033, P032, P031, P030, P029, P028, P027, Function.update]
  dsimp only [P026, P025, P024, P023, P022, P021, P020, P019, Function.update]
  dsimp only [P018, P017, P016, P015, P014, P013, P012, P011, Function.update]
  dsimp only [P010, P009, P008, P007, P006, P005, P004, P003, Function.update]
  dsimp only [P002, P001, P000, Function.update]
  rfl
theorem consumer042 : C042 700 = 0#u8 := by
  dsimp only [C042, C041, C040, C039, C038, C037, C036, C035, Function.update]
  dsimp only [C034, C033, C032, C031, C030, C029, C028, C027, Function.update]
  dsimp only [C026, C025, C024, C023, C022, C021, C020, C019, Function.update]
  dsimp only [C018, C017, C016, C015, C014, C013, C012, C011, Function.update]
  dsimp only [C010, C009, C008, C007, C006, C005, C004, C003, Function.update]
  dsimp only [C002, C001, C000, Function.update]
  rfl
theorem step042 : body s042 = ok (cont s043) := by
  unfold body s042 s043 P043 C043 M043
  have next : Usize.wrapping_add 42#usize 1#usize = 43#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 42#usize (by
      change 43 < Usize.size; simpa using UScalar.hSize (43#usize))
  simpa only [next, show (683#usize).val = 683 from rfl,
    show (700#usize).val = 700 from rfl] using step P042 C042 M042 42#usize 683#usize 700#usize 683#u16 700#u16 1#u8 1#u8
    (by decide) link042 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P042 683) = _; rw [producer042]; rfl) (by change host_forest.mask_endpoint_bump (C042 700) = _; rw [consumer042]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link043 : Array.index_usize host_forest.MASK_LINKS 43#usize = ok (683#u16,688#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer043 : P043 683 = 1#u8 := by
  dsimp only [P043, P042, P041, P040, P039, P038, P037, P036, Function.update]
  dsimp only [P035, P034, P033, P032, P031, P030, P029, P028, Function.update]
  dsimp only [P027, P026, P025, P024, P023, P022, P021, P020, Function.update]
  dsimp only [P019, P018, P017, P016, P015, P014, P013, P012, Function.update]
  dsimp only [P011, P010, P009, P008, P007, P006, P005, P004, Function.update]
  dsimp only [P003, P002, P001, P000, Function.update]
  rfl
theorem consumer043 : C043 688 = 0#u8 := by
  dsimp only [C043, C042, C041, C040, C039, C038, C037, C036, Function.update]
  dsimp only [C035, C034, C033, C032, C031, C030, C029, C028, Function.update]
  dsimp only [C027, C026, C025, C024, C023, C022, C021, C020, Function.update]
  dsimp only [C019, C018, C017, C016, C015, C014, C013, C012, Function.update]
  dsimp only [C011, C010, C009, C008, C007, C006, C005, C004, Function.update]
  dsimp only [C003, C002, C001, C000, Function.update]
  rfl
theorem step043 : body s043 = ok (cont s044) := by
  unfold body s043 s044 P044 C044 M044
  have next : Usize.wrapping_add 43#usize 1#usize = 44#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 43#usize (by
      change 44 < Usize.size; simpa using UScalar.hSize (44#usize))
  simpa only [next, show (683#usize).val = 683 from rfl,
    show (688#usize).val = 688 from rfl] using step P043 C043 M043 43#usize 683#usize 688#usize 683#u16 688#u16 2#u8 1#u8
    (by decide) link043 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P043 683) = _; rw [producer043]; rfl) (by change host_forest.mask_endpoint_bump (C043 688) = _; rw [consumer043]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link044 : Array.index_usize host_forest.MASK_LINKS 44#usize = ok (699#u16,716#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer044 : P044 699 = 0#u8 := by
  dsimp only [P044, P043, P042, P041, P040, P039, P038, P037, Function.update]
  dsimp only [P036, P035, P034, P033, P032, P031, P030, P029, Function.update]
  dsimp only [P028, P027, P026, P025, P024, P023, P022, P021, Function.update]
  dsimp only [P020, P019, P018, P017, P016, P015, P014, P013, Function.update]
  dsimp only [P012, P011, P010, P009, P008, P007, P006, P005, Function.update]
  dsimp only [P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer044 : C044 716 = 0#u8 := by
  dsimp only [C044, C043, C042, C041, C040, C039, C038, C037, Function.update]
  dsimp only [C036, C035, C034, C033, C032, C031, C030, C029, Function.update]
  dsimp only [C028, C027, C026, C025, C024, C023, C022, C021, Function.update]
  dsimp only [C020, C019, C018, C017, C016, C015, C014, C013, Function.update]
  dsimp only [C012, C011, C010, C009, C008, C007, C006, C005, Function.update]
  dsimp only [C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step044 : body s044 = ok (cont s045) := by
  unfold body s044 s045 P045 C045 M045
  have next : Usize.wrapping_add 44#usize 1#usize = 45#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 44#usize (by
      change 45 < Usize.size; simpa using UScalar.hSize (45#usize))
  simpa only [next, show (699#usize).val = 699 from rfl,
    show (716#usize).val = 716 from rfl] using step P044 C044 M044 44#usize 699#usize 716#usize 699#u16 716#u16 1#u8 1#u8
    (by decide) link044 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P044 699) = _; rw [producer044]; rfl) (by change host_forest.mask_endpoint_bump (C044 716) = _; rw [consumer044]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link045 : Array.index_usize host_forest.MASK_LINKS 45#usize = ok (699#u16,704#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer045 : P045 699 = 1#u8 := by
  dsimp only [P045, P044, P043, P042, P041, P040, P039, P038, Function.update]
  dsimp only [P037, P036, P035, P034, P033, P032, P031, P030, Function.update]
  dsimp only [P029, P028, P027, P026, P025, P024, P023, P022, Function.update]
  dsimp only [P021, P020, P019, P018, P017, P016, P015, P014, Function.update]
  dsimp only [P013, P012, P011, P010, P009, P008, P007, P006, Function.update]
  dsimp only [P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer045 : C045 704 = 0#u8 := by
  dsimp only [C045, C044, C043, C042, C041, C040, C039, C038, Function.update]
  dsimp only [C037, C036, C035, C034, C033, C032, C031, C030, Function.update]
  dsimp only [C029, C028, C027, C026, C025, C024, C023, C022, Function.update]
  dsimp only [C021, C020, C019, C018, C017, C016, C015, C014, Function.update]
  dsimp only [C013, C012, C011, C010, C009, C008, C007, C006, Function.update]
  dsimp only [C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step045 : body s045 = ok (cont s046) := by
  unfold body s045 s046 P046 C046 M046
  have next : Usize.wrapping_add 45#usize 1#usize = 46#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 45#usize (by
      change 46 < Usize.size; simpa using UScalar.hSize (46#usize))
  simpa only [next, show (699#usize).val = 699 from rfl,
    show (704#usize).val = 704 from rfl] using step P045 C045 M045 45#usize 699#usize 704#usize 699#u16 704#u16 2#u8 1#u8
    (by decide) link045 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P045 699) = _; rw [producer045]; rfl) (by change host_forest.mask_endpoint_bump (C045 704) = _; rw [consumer045]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link046 : Array.index_usize host_forest.MASK_LINKS 46#usize = ok (715#u16,732#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer046 : P046 715 = 0#u8 := by
  dsimp only [P046, P045, P044, P043, P042, P041, P040, P039, Function.update]
  dsimp only [P038, P037, P036, P035, P034, P033, P032, P031, Function.update]
  dsimp only [P030, P029, P028, P027, P026, P025, P024, P023, Function.update]
  dsimp only [P022, P021, P020, P019, P018, P017, P016, P015, Function.update]
  dsimp only [P014, P013, P012, P011, P010, P009, P008, P007, Function.update]
  dsimp only [P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer046 : C046 732 = 0#u8 := by
  dsimp only [C046, C045, C044, C043, C042, C041, C040, C039, Function.update]
  dsimp only [C038, C037, C036, C035, C034, C033, C032, C031, Function.update]
  dsimp only [C030, C029, C028, C027, C026, C025, C024, C023, Function.update]
  dsimp only [C022, C021, C020, C019, C018, C017, C016, C015, Function.update]
  dsimp only [C014, C013, C012, C011, C010, C009, C008, C007, Function.update]
  dsimp only [C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step046 : body s046 = ok (cont s047) := by
  unfold body s046 s047 P047 C047 M047
  have next : Usize.wrapping_add 46#usize 1#usize = 47#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 46#usize (by
      change 47 < Usize.size; simpa using UScalar.hSize (47#usize))
  simpa only [next, show (715#usize).val = 715 from rfl,
    show (732#usize).val = 732 from rfl] using step P046 C046 M046 46#usize 715#usize 732#usize 715#u16 732#u16 1#u8 1#u8
    (by decide) link046 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P046 715) = _; rw [producer046]; rfl) (by change host_forest.mask_endpoint_bump (C046 732) = _; rw [consumer046]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link047 : Array.index_usize host_forest.MASK_LINKS 47#usize = ok (715#u16,720#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer047 : P047 715 = 1#u8 := by
  dsimp only [P047, P046, P045, P044, P043, P042, P041, P040, Function.update]
  dsimp only [P039, P038, P037, P036, P035, P034, P033, P032, Function.update]
  dsimp only [P031, P030, P029, P028, P027, P026, P025, P024, Function.update]
  dsimp only [P023, P022, P021, P020, P019, P018, P017, P016, Function.update]
  dsimp only [P015, P014, P013, P012, P011, P010, P009, P008, Function.update]
  dsimp only [P007, P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer047 : C047 720 = 0#u8 := by
  dsimp only [C047, C046, C045, C044, C043, C042, C041, C040, Function.update]
  dsimp only [C039, C038, C037, C036, C035, C034, C033, C032, Function.update]
  dsimp only [C031, C030, C029, C028, C027, C026, C025, C024, Function.update]
  dsimp only [C023, C022, C021, C020, C019, C018, C017, C016, Function.update]
  dsimp only [C015, C014, C013, C012, C011, C010, C009, C008, Function.update]
  dsimp only [C007, C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step047 : body s047 = ok (cont s048) := by
  unfold body s047 s048 P048 C048 M048
  have next : Usize.wrapping_add 47#usize 1#usize = 48#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 47#usize (by
      change 48 < Usize.size; simpa using UScalar.hSize (48#usize))
  simpa only [next, show (715#usize).val = 715 from rfl,
    show (720#usize).val = 720 from rfl] using step P047 C047 M047 47#usize 715#usize 720#usize 715#u16 720#u16 2#u8 1#u8
    (by decide) link047 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P047 715) = _; rw [producer047]; rfl) (by change host_forest.mask_endpoint_bump (C047 720) = _; rw [consumer047]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s040 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step040).trans ((run_next _ _ step041).trans ((run_next _ _ step042).trans ((run_next _ _ step043).trans ((run_next _ _ step044).trans ((run_next _ _ step045).trans ((run_next _ _ step046).trans ((run_next _ _ step047).trans (PV_B3_MaskSparse06.suffix))))))))
#print axioms link040
#print axioms producer040
#print axioms consumer040
#print axioms step040
#print axioms link041
#print axioms producer041
#print axioms consumer041
#print axioms step041
#print axioms link042
#print axioms producer042
#print axioms consumer042
#print axioms step042
#print axioms link043
#print axioms producer043
#print axioms consumer043
#print axioms step043
#print axioms link044
#print axioms producer044
#print axioms consumer044
#print axioms step044
#print axioms link045
#print axioms producer045
#print axioms consumer045
#print axioms step045
#print axioms link046
#print axioms producer046
#print axioms consumer046
#print axioms step046
#print axioms link047
#print axioms producer047
#print axioms consumer047
#print axioms step047
#print axioms suffix
end PV_B3_MaskSparse05
