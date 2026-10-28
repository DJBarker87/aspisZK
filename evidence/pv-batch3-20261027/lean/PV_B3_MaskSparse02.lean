import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse03
namespace PV_B3_MaskSparse02
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link016 : Array.index_usize host_forest.MASK_LINKS 16#usize = ok (1012#u16,1015#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer016 : P016 1012 = 0#u8 := by
  dsimp only [P016, P015, P014, P013, P012, P011, P010, P009, Function.update]
  dsimp only [P008, P007, P006, P005, P004, P003, P002, P001, Function.update]
  dsimp only [P000, Function.update]
  rfl
theorem consumer016 : C016 1015 = 0#u8 := by
  dsimp only [C016, C015, C014, C013, C012, C011, C010, C009, Function.update]
  dsimp only [C008, C007, C006, C005, C004, C003, C002, C001, Function.update]
  dsimp only [C000, Function.update]
  rfl
theorem step016 : body s016 = ok (cont s017) := by
  unfold body s016 s017 P017 C017 M017
  have next : Usize.wrapping_add 16#usize 1#usize = 17#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 16#usize (by
      change 17 < Usize.size; simpa using UScalar.hSize (17#usize))
  simpa only [next, show (1012#usize).val = 1012 from rfl,
    show (1015#usize).val = 1015 from rfl] using step P016 C016 M016 16#usize 1012#usize 1015#usize 1012#u16 1015#u16 1#u8 1#u8
    (by decide) link016 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P016 1012) = _; rw [producer016]; rfl) (by change host_forest.mask_endpoint_bump (C016 1015) = _; rw [consumer016]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link017 : Array.index_usize host_forest.MASK_LINKS 17#usize = ok (1014#u16,1015#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer017 : P017 1014 = 0#u8 := by
  dsimp only [P017, P016, P015, P014, P013, P012, P011, P010, Function.update]
  dsimp only [P009, P008, P007, P006, P005, P004, P003, P002, Function.update]
  dsimp only [P001, P000, Function.update]
  rfl
theorem consumer017 : C017 1015 = 1#u8 := by
  dsimp only [C017, C016, C015, C014, C013, C012, C011, C010, Function.update]
  dsimp only [C009, C008, C007, C006, C005, C004, C003, C002, Function.update]
  dsimp only [C001, C000, Function.update]
  rfl
theorem step017 : body s017 = ok (cont s018) := by
  unfold body s017 s018 P018 C018 M018
  have next : Usize.wrapping_add 17#usize 1#usize = 18#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 17#usize (by
      change 18 < Usize.size; simpa using UScalar.hSize (18#usize))
  simpa only [next, show (1014#usize).val = 1014 from rfl,
    show (1015#usize).val = 1015 from rfl] using step P017 C017 M017 17#usize 1014#usize 1015#usize 1014#u16 1015#u16 1#u8 2#u8
    (by decide) link017 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P017 1014) = _; rw [producer017]; rfl) (by change host_forest.mask_endpoint_bump (C017 1015) = _; rw [consumer017]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link018 : Array.index_usize host_forest.MASK_LINKS 18#usize = ok (64#u16,1017#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer018 : P018 64 = 0#u8 := by
  dsimp only [P018, P017, P016, P015, P014, P013, P012, P011, Function.update]
  dsimp only [P010, P009, P008, P007, P006, P005, P004, P003, Function.update]
  dsimp only [P002, P001, P000, Function.update]
  rfl
theorem consumer018 : C018 1017 = 0#u8 := by
  dsimp only [C018, C017, C016, C015, C014, C013, C012, C011, Function.update]
  dsimp only [C010, C009, C008, C007, C006, C005, C004, C003, Function.update]
  dsimp only [C002, C001, C000, Function.update]
  rfl
theorem step018 : body s018 = ok (cont s019) := by
  unfold body s018 s019 P019 C019 M019
  have next : Usize.wrapping_add 18#usize 1#usize = 19#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 18#usize (by
      change 19 < Usize.size; simpa using UScalar.hSize (19#usize))
  simpa only [next, show (64#usize).val = 64 from rfl,
    show (1017#usize).val = 1017 from rfl] using step P018 C018 M018 18#usize 64#usize 1017#usize 64#u16 1017#u16 1#u8 1#u8
    (by decide) link018 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P018 64) = _; rw [producer018]; rfl) (by change host_forest.mask_endpoint_bump (C018 1017) = _; rw [consumer018]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link019 : Array.index_usize host_forest.MASK_LINKS 19#usize = ok (913#u16,1017#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer019 : P019 913 = 0#u8 := by
  dsimp only [P019, P018, P017, P016, P015, P014, P013, P012, Function.update]
  dsimp only [P011, P010, P009, P008, P007, P006, P005, P004, Function.update]
  dsimp only [P003, P002, P001, P000, Function.update]
  rfl
theorem consumer019 : C019 1017 = 1#u8 := by
  dsimp only [C019, C018, C017, C016, C015, C014, C013, C012, Function.update]
  dsimp only [C011, C010, C009, C008, C007, C006, C005, C004, Function.update]
  dsimp only [C003, C002, C001, C000, Function.update]
  rfl
theorem step019 : body s019 = ok (cont s020) := by
  unfold body s019 s020 P020 C020 M020
  have next : Usize.wrapping_add 19#usize 1#usize = 20#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 19#usize (by
      change 20 < Usize.size; simpa using UScalar.hSize (20#usize))
  simpa only [next, show (913#usize).val = 913 from rfl,
    show (1017#usize).val = 1017 from rfl] using step P019 C019 M019 19#usize 913#usize 1017#usize 913#u16 1017#u16 1#u8 2#u8
    (by decide) link019 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P019 913) = _; rw [producer019]; rfl) (by change host_forest.mask_endpoint_bump (C019 1017) = _; rw [consumer019]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link020 : Array.index_usize host_forest.MASK_LINKS 20#usize = ok (523#u16,1018#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer020 : P020 523 = 0#u8 := by
  dsimp only [P020, P019, P018, P017, P016, P015, P014, P013, Function.update]
  dsimp only [P012, P011, P010, P009, P008, P007, P006, P005, Function.update]
  dsimp only [P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer020 : C020 1018 = 0#u8 := by
  dsimp only [C020, C019, C018, C017, C016, C015, C014, C013, Function.update]
  dsimp only [C012, C011, C010, C009, C008, C007, C006, C005, Function.update]
  dsimp only [C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step020 : body s020 = ok (cont s021) := by
  unfold body s020 s021 P021 C021 M021
  have next : Usize.wrapping_add 20#usize 1#usize = 21#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 20#usize (by
      change 21 < Usize.size; simpa using UScalar.hSize (21#usize))
  simpa only [next, show (523#usize).val = 523 from rfl,
    show (1018#usize).val = 1018 from rfl] using step P020 C020 M020 20#usize 523#usize 1018#usize 523#u16 1018#u16 1#u8 1#u8
    (by decide) link020 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P020 523) = _; rw [producer020]; rfl) (by change host_forest.mask_endpoint_bump (C020 1018) = _; rw [consumer020]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link021 : Array.index_usize host_forest.MASK_LINKS 21#usize = ok (475#u16,540#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer021 : P021 475 = 0#u8 := by
  dsimp only [P021, P020, P019, P018, P017, P016, P015, P014, Function.update]
  dsimp only [P013, P012, P011, P010, P009, P008, P007, P006, Function.update]
  dsimp only [P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer021 : C021 540 = 0#u8 := by
  dsimp only [C021, C020, C019, C018, C017, C016, C015, C014, Function.update]
  dsimp only [C013, C012, C011, C010, C009, C008, C007, C006, Function.update]
  dsimp only [C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step021 : body s021 = ok (cont s022) := by
  unfold body s021 s022 P022 C022 M022
  have next : Usize.wrapping_add 21#usize 1#usize = 22#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 21#usize (by
      change 22 < Usize.size; simpa using UScalar.hSize (22#usize))
  simpa only [next, show (475#usize).val = 475 from rfl,
    show (540#usize).val = 540 from rfl] using step P021 C021 M021 21#usize 475#usize 540#usize 475#u16 540#u16 1#u8 1#u8
    (by decide) link021 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P021 475) = _; rw [producer021]; rfl) (by change host_forest.mask_endpoint_bump (C021 540) = _; rw [consumer021]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link022 : Array.index_usize host_forest.MASK_LINKS 22#usize = ok (523#u16,540#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer022 : P022 523 = 1#u8 := by
  dsimp only [P022, P021, P020, P019, P018, P017, P016, P015, Function.update]
  dsimp only [P014, P013, P012, P011, P010, P009, P008, P007, Function.update]
  dsimp only [P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer022 : C022 540 = 1#u8 := by
  dsimp only [C022, C021, C020, C019, C018, C017, C016, C015, Function.update]
  dsimp only [C014, C013, C012, C011, C010, C009, C008, C007, Function.update]
  dsimp only [C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step022 : body s022 = ok (cont s023) := by
  unfold body s022 s023 P023 C023 M023
  have next : Usize.wrapping_add 22#usize 1#usize = 23#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 22#usize (by
      change 23 < Usize.size; simpa using UScalar.hSize (23#usize))
  simpa only [next, show (523#usize).val = 523 from rfl,
    show (540#usize).val = 540 from rfl] using step P022 C022 M022 22#usize 523#usize 540#usize 523#u16 540#u16 2#u8 2#u8
    (by decide) link022 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P022 523) = _; rw [producer022]; rfl) (by change host_forest.mask_endpoint_bump (C022 540) = _; rw [consumer022]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link023 : Array.index_usize host_forest.MASK_LINKS 23#usize = ok (1018#u16,528#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer023 : P023 1018 = 0#u8 := by
  dsimp only [P023, P022, P021, P020, P019, P018, P017, P016, Function.update]
  dsimp only [P015, P014, P013, P012, P011, P010, P009, P008, Function.update]
  dsimp only [P007, P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer023 : C023 528 = 0#u8 := by
  dsimp only [C023, C022, C021, C020, C019, C018, C017, C016, Function.update]
  dsimp only [C015, C014, C013, C012, C011, C010, C009, C008, Function.update]
  dsimp only [C007, C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step023 : body s023 = ok (cont s024) := by
  unfold body s023 s024 P024 C024 M024
  have next : Usize.wrapping_add 23#usize 1#usize = 24#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 23#usize (by
      change 24 < Usize.size; simpa using UScalar.hSize (24#usize))
  simpa only [next, show (1018#usize).val = 1018 from rfl,
    show (528#usize).val = 528 from rfl] using step P023 C023 M023 23#usize 1018#usize 528#usize 1018#u16 528#u16 1#u8 1#u8
    (by decide) link023 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P023 1018) = _; rw [producer023]; rfl) (by change host_forest.mask_endpoint_bump (C023 528) = _; rw [consumer023]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s016 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step016).trans ((run_next _ _ step017).trans ((run_next _ _ step018).trans ((run_next _ _ step019).trans ((run_next _ _ step020).trans ((run_next _ _ step021).trans ((run_next _ _ step022).trans ((run_next _ _ step023).trans (PV_B3_MaskSparse03.suffix))))))))
#print axioms link016
#print axioms producer016
#print axioms consumer016
#print axioms step016
#print axioms link017
#print axioms producer017
#print axioms consumer017
#print axioms step017
#print axioms link018
#print axioms producer018
#print axioms consumer018
#print axioms step018
#print axioms link019
#print axioms producer019
#print axioms consumer019
#print axioms step019
#print axioms link020
#print axioms producer020
#print axioms consumer020
#print axioms step020
#print axioms link021
#print axioms producer021
#print axioms consumer021
#print axioms step021
#print axioms link022
#print axioms producer022
#print axioms consumer022
#print axioms step022
#print axioms link023
#print axioms producer023
#print axioms consumer023
#print axioms step023
#print axioms suffix
end PV_B3_MaskSparse02
