import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse02
namespace PV_B3_MaskSparse01
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link008 : Array.index_usize host_forest.MASK_LINKS 8#usize = ok (12#u16,412#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer008 : P008 12 = 0#u8 := by
  dsimp only [P008, P007, P006, P005, P004, P003, P002, P001, Function.update]
  dsimp only [P000, Function.update]
  rfl
theorem consumer008 : C008 412 = 0#u8 := by
  dsimp only [C008, C007, C006, C005, C004, C003, C002, C001, Function.update]
  dsimp only [C000, Function.update]
  rfl
theorem step008 : body s008 = ok (cont s009) := by
  unfold body s008 s009 P009 C009 M009
  have next : Usize.wrapping_add 8#usize 1#usize = 9#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 8#usize (by
      change 9 < Usize.size; simpa using UScalar.hSize (9#usize))
  simpa only [next, show (12#usize).val = 12 from rfl,
    show (412#usize).val = 412 from rfl] using step P008 C008 M008 8#usize 12#usize 412#usize 12#u16 412#u16 1#u8 1#u8
    (by decide) link008 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P008 12) = _; rw [producer008]; rfl) (by change host_forest.mask_endpoint_bump (C008 412) = _; rw [consumer008]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link009 : Array.index_usize host_forest.MASK_LINKS 9#usize = ok (44#u16,428#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer009 : P009 44 = 0#u8 := by
  dsimp only [P009, P008, P007, P006, P005, P004, P003, P002, Function.update]
  dsimp only [P001, P000, Function.update]
  rfl
theorem consumer009 : C009 428 = 0#u8 := by
  dsimp only [C009, C008, C007, C006, C005, C004, C003, C002, Function.update]
  dsimp only [C001, C000, Function.update]
  rfl
theorem step009 : body s009 = ok (cont s010) := by
  unfold body s009 s010 P010 C010 M010
  have next : Usize.wrapping_add 9#usize 1#usize = 10#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 9#usize (by
      change 10 < Usize.size; simpa using UScalar.hSize (10#usize))
  simpa only [next, show (44#usize).val = 44 from rfl,
    show (428#usize).val = 428 from rfl] using step P009 C009 M009 9#usize 44#usize 428#usize 44#u16 428#u16 1#u8 1#u8
    (by decide) link009 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P009 44) = _; rw [producer009]; rfl) (by change host_forest.mask_endpoint_bump (C009 428) = _; rw [consumer009]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link010 : Array.index_usize host_forest.MASK_LINKS 10#usize = ok (60#u16,428#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer010 : P010 60 = 0#u8 := by
  dsimp only [P010, P009, P008, P007, P006, P005, P004, P003, Function.update]
  dsimp only [P002, P001, P000, Function.update]
  rfl
theorem consumer010 : C010 428 = 1#u8 := by
  dsimp only [C010, C009, C008, C007, C006, C005, C004, C003, Function.update]
  dsimp only [C002, C001, C000, Function.update]
  rfl
theorem step010 : body s010 = ok (cont s011) := by
  unfold body s010 s011 P011 C011 M011
  have next : Usize.wrapping_add 10#usize 1#usize = 11#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 10#usize (by
      change 11 < Usize.size; simpa using UScalar.hSize (11#usize))
  simpa only [next, show (60#usize).val = 60 from rfl,
    show (428#usize).val = 428 from rfl] using step P010 C010 M010 10#usize 60#usize 428#usize 60#u16 428#u16 1#u8 2#u8
    (by decide) link010 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P010 60) = _; rw [producer010]; rfl) (by change host_forest.mask_endpoint_bump (C010 428) = _; rw [consumer010]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link011 : Array.index_usize host_forest.MASK_LINKS 11#usize = ok (44#u16,1008#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer011 : P011 44 = 1#u8 := by
  dsimp only [P011, P010, P009, P008, P007, P006, P005, P004, Function.update]
  dsimp only [P003, P002, P001, P000, Function.update]
  rfl
theorem consumer011 : C011 1008 = 0#u8 := by
  dsimp only [C011, C010, C009, C008, C007, C006, C005, C004, Function.update]
  dsimp only [C003, C002, C001, C000, Function.update]
  rfl
theorem step011 : body s011 = ok (cont s012) := by
  unfold body s011 s012 P012 C012 M012
  have next : Usize.wrapping_add 11#usize 1#usize = 12#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 11#usize (by
      change 12 < Usize.size; simpa using UScalar.hSize (12#usize))
  simpa only [next, show (44#usize).val = 44 from rfl,
    show (1008#usize).val = 1008 from rfl] using step P011 C011 M011 11#usize 44#usize 1008#usize 44#u16 1008#u16 2#u8 1#u8
    (by decide) link011 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P011 44) = _; rw [producer011]; rfl) (by change host_forest.mask_endpoint_bump (C011 1008) = _; rw [consumer011]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link012 : Array.index_usize host_forest.MASK_LINKS 12#usize = ok (460#u16,1010#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer012 : P012 460 = 0#u8 := by
  dsimp only [P012, P011, P010, P009, P008, P007, P006, P005, Function.update]
  dsimp only [P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer012 : C012 1010 = 0#u8 := by
  dsimp only [C012, C011, C010, C009, C008, C007, C006, C005, Function.update]
  dsimp only [C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step012 : body s012 = ok (cont s013) := by
  unfold body s012 s013 P013 C013 M013
  have next : Usize.wrapping_add 12#usize 1#usize = 13#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 12#usize (by
      change 13 < Usize.size; simpa using UScalar.hSize (13#usize))
  simpa only [next, show (460#usize).val = 460 from rfl,
    show (1010#usize).val = 1010 from rfl] using step P012 C012 M012 12#usize 460#usize 1010#usize 460#u16 1010#u16 1#u8 1#u8
    (by decide) link012 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P012 460) = _; rw [producer012]; rfl) (by change host_forest.mask_endpoint_bump (C012 1010) = _; rw [consumer012]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link013 : Array.index_usize host_forest.MASK_LINKS 13#usize = ok (508#u16,1012#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer013 : P013 508 = 0#u8 := by
  dsimp only [P013, P012, P011, P010, P009, P008, P007, P006, Function.update]
  dsimp only [P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer013 : C013 1012 = 0#u8 := by
  dsimp only [C013, C012, C011, C010, C009, C008, C007, C006, Function.update]
  dsimp only [C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step013 : body s013 = ok (cont s014) := by
  unfold body s013 s014 P014 C014 M014
  have next : Usize.wrapping_add 13#usize 1#usize = 14#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 13#usize (by
      change 14 < Usize.size; simpa using UScalar.hSize (14#usize))
  simpa only [next, show (508#usize).val = 508 from rfl,
    show (1012#usize).val = 1012 from rfl] using step P013 C013 M013 13#usize 508#usize 1012#usize 508#u16 1012#u16 1#u8 1#u8
    (by decide) link013 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P013 508) = _; rw [producer013]; rfl) (by change host_forest.mask_endpoint_bump (C013 1012) = _; rw [consumer013]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link014 : Array.index_usize host_forest.MASK_LINKS 14#usize = ok (1008#u16,1014#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer014 : P014 1008 = 0#u8 := by
  dsimp only [P014, P013, P012, P011, P010, P009, P008, P007, Function.update]
  dsimp only [P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer014 : C014 1014 = 0#u8 := by
  dsimp only [C014, C013, C012, C011, C010, C009, C008, C007, Function.update]
  dsimp only [C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step014 : body s014 = ok (cont s015) := by
  unfold body s014 s015 P015 C015 M015
  have next : Usize.wrapping_add 14#usize 1#usize = 15#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 14#usize (by
      change 15 < Usize.size; simpa using UScalar.hSize (15#usize))
  simpa only [next, show (1008#usize).val = 1008 from rfl,
    show (1014#usize).val = 1014 from rfl] using step P014 C014 M014 14#usize 1008#usize 1014#usize 1008#u16 1014#u16 1#u8 1#u8
    (by decide) link014 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P014 1008) = _; rw [producer014]; rfl) (by change host_forest.mask_endpoint_bump (C014 1014) = _; rw [consumer014]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link015 : Array.index_usize host_forest.MASK_LINKS 15#usize = ok (1010#u16,1014#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer015 : P015 1010 = 0#u8 := by
  dsimp only [P015, P014, P013, P012, P011, P010, P009, P008, Function.update]
  dsimp only [P007, P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer015 : C015 1014 = 1#u8 := by
  dsimp only [C015, C014, C013, C012, C011, C010, C009, C008, Function.update]
  dsimp only [C007, C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step015 : body s015 = ok (cont s016) := by
  unfold body s015 s016 P016 C016 M016
  have next : Usize.wrapping_add 15#usize 1#usize = 16#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 15#usize (by
      change 16 < Usize.size; simpa using UScalar.hSize (16#usize))
  simpa only [next, show (1010#usize).val = 1010 from rfl,
    show (1014#usize).val = 1014 from rfl] using step P015 C015 M015 15#usize 1010#usize 1014#usize 1010#u16 1014#u16 1#u8 2#u8
    (by decide) link015 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P015 1010) = _; rw [producer015]; rfl) (by change host_forest.mask_endpoint_bump (C015 1014) = _; rw [consumer015]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s008 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step008).trans ((run_next _ _ step009).trans ((run_next _ _ step010).trans ((run_next _ _ step011).trans ((run_next _ _ step012).trans ((run_next _ _ step013).trans ((run_next _ _ step014).trans ((run_next _ _ step015).trans (PV_B3_MaskSparse02.suffix))))))))
#print axioms link008
#print axioms producer008
#print axioms consumer008
#print axioms step008
#print axioms link009
#print axioms producer009
#print axioms consumer009
#print axioms step009
#print axioms link010
#print axioms producer010
#print axioms consumer010
#print axioms step010
#print axioms link011
#print axioms producer011
#print axioms consumer011
#print axioms step011
#print axioms link012
#print axioms producer012
#print axioms consumer012
#print axioms step012
#print axioms link013
#print axioms producer013
#print axioms consumer013
#print axioms step013
#print axioms link014
#print axioms producer014
#print axioms consumer014
#print axioms step014
#print axioms link015
#print axioms producer015
#print axioms consumer015
#print axioms step015
#print axioms suffix
end PV_B3_MaskSparse01
