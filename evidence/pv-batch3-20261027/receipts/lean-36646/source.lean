import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse01
namespace PV_B3_MaskSparse00
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link000 : Array.index_usize host_forest.MASK_LINKS 0#usize = ok (27#u16,32#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer000 : P000 27 = 0#u8 := by
  dsimp only [P000, Function.update]
  rfl
theorem consumer000 : C000 32 = 0#u8 := by
  dsimp only [C000, Function.update]
  rfl
theorem step000 : body s000 = ok (cont s001) := by
  unfold body s000 s001 P001 C001 M001
  have next : Usize.wrapping_add 0#usize 1#usize = 1#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 0#usize (by
      change 1 < Usize.size; simpa using UScalar.hSize (1#usize))
  simpa only [next, show (27#usize).val = 27 from rfl,
    show (32#usize).val = 32 from rfl] using step P000 C000 M000 0#usize 27#usize 32#usize 27#u16 32#u16 1#u8 1#u8
    (by decide) link000 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P000 27) = _; rw [producer000]; rfl) (by change host_forest.mask_endpoint_bump (C000 32) = _; rw [consumer000]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link001 : Array.index_usize host_forest.MASK_LINKS 1#usize = ok (43#u16,48#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer001 : P001 43 = 0#u8 := by
  dsimp only [P001, P000, Function.update]
  rfl
theorem consumer001 : C001 48 = 0#u8 := by
  dsimp only [C001, C000, Function.update]
  rfl
theorem step001 : body s001 = ok (cont s002) := by
  unfold body s001 s002 P002 C002 M002
  have next : Usize.wrapping_add 1#usize 1#usize = 2#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 1#usize (by
      change 2 < Usize.size; simpa using UScalar.hSize (2#usize))
  simpa only [next, show (43#usize).val = 43 from rfl,
    show (48#usize).val = 48 from rfl] using step P001 C001 M001 1#usize 43#usize 48#usize 43#u16 48#u16 1#u8 1#u8
    (by decide) link001 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P001 43) = _; rw [producer001]; rfl) (by change host_forest.mask_endpoint_bump (C001 48) = _; rw [consumer001]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link002 : Array.index_usize host_forest.MASK_LINKS 2#usize = ok (411#u16,416#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer002 : P002 411 = 0#u8 := by
  dsimp only [P002, P001, P000, Function.update]
  rfl
theorem consumer002 : C002 416 = 0#u8 := by
  dsimp only [C002, C001, C000, Function.update]
  rfl
theorem step002 : body s002 = ok (cont s003) := by
  unfold body s002 s003 P003 C003 M003
  have next : Usize.wrapping_add 2#usize 1#usize = 3#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 2#usize (by
      change 3 < Usize.size; simpa using UScalar.hSize (3#usize))
  simpa only [next, show (411#usize).val = 411 from rfl,
    show (416#usize).val = 416 from rfl] using step P002 C002 M002 2#usize 411#usize 416#usize 411#u16 416#u16 1#u8 1#u8
    (by decide) link002 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P002 411) = _; rw [producer002]; rfl) (by change host_forest.mask_endpoint_bump (C002 416) = _; rw [consumer002]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link003 : Array.index_usize host_forest.MASK_LINKS 3#usize = ok (443#u16,448#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer003 : P003 443 = 0#u8 := by
  dsimp only [P003, P002, P001, P000, Function.update]
  rfl
theorem consumer003 : C003 448 = 0#u8 := by
  dsimp only [C003, C002, C001, C000, Function.update]
  rfl
theorem step003 : body s003 = ok (cont s004) := by
  unfold body s003 s004 P004 C004 M004
  have next : Usize.wrapping_add 3#usize 1#usize = 4#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 3#usize (by
      change 4 < Usize.size; simpa using UScalar.hSize (4#usize))
  simpa only [next, show (443#usize).val = 443 from rfl,
    show (448#usize).val = 448 from rfl] using step P003 C003 M003 3#usize 443#usize 448#usize 443#u16 448#u16 1#u8 1#u8
    (by decide) link003 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P003 443) = _; rw [producer003]; rfl) (by change host_forest.mask_endpoint_bump (C003 448) = _; rw [consumer003]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link004 : Array.index_usize host_forest.MASK_LINKS 4#usize = ok (459#u16,464#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer004 : P004 459 = 0#u8 := by
  dsimp only [P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer004 : C004 464 = 0#u8 := by
  dsimp only [C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step004 : body s004 = ok (cont s005) := by
  unfold body s004 s005 P005 C005 M005
  have next : Usize.wrapping_add 4#usize 1#usize = 5#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 4#usize (by
      change 5 < Usize.size; simpa using UScalar.hSize (5#usize))
  simpa only [next, show (459#usize).val = 459 from rfl,
    show (464#usize).val = 464 from rfl] using step P004 C004 M004 4#usize 459#usize 464#usize 459#u16 464#u16 1#u8 1#u8
    (by decide) link004 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P004 459) = _; rw [producer004]; rfl) (by change host_forest.mask_endpoint_bump (C004 464) = _; rw [consumer004]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link005 : Array.index_usize host_forest.MASK_LINKS 5#usize = ok (491#u16,496#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer005 : P005 491 = 0#u8 := by
  dsimp only [P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer005 : C005 496 = 0#u8 := by
  dsimp only [C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step005 : body s005 = ok (cont s006) := by
  unfold body s005 s006 P006 C006 M006
  have next : Usize.wrapping_add 5#usize 1#usize = 6#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 5#usize (by
      change 6 < Usize.size; simpa using UScalar.hSize (6#usize))
  simpa only [next, show (491#usize).val = 491 from rfl,
    show (496#usize).val = 496 from rfl] using step P005 C005 M005 5#usize 491#usize 496#usize 491#u16 496#u16 1#u8 1#u8
    (by decide) link005 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P005 491) = _; rw [producer005]; rfl) (by change host_forest.mask_endpoint_bump (C005 496) = _; rw [consumer005]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link006 : Array.index_usize host_forest.MASK_LINKS 6#usize = ok (507#u16,512#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer006 : P006 507 = 0#u8 := by
  dsimp only [P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer006 : C006 512 = 0#u8 := by
  dsimp only [C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step006 : body s006 = ok (cont s007) := by
  unfold body s006 s007 P007 C007 M007
  have next : Usize.wrapping_add 6#usize 1#usize = 7#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 6#usize (by
      change 7 < Usize.size; simpa using UScalar.hSize (7#usize))
  simpa only [next, show (507#usize).val = 507 from rfl,
    show (512#usize).val = 512 from rfl] using step P006 C006 M006 6#usize 507#usize 512#usize 507#u16 512#u16 1#u8 1#u8
    (by decide) link006 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P006 507) = _; rw [producer006]; rfl) (by change host_forest.mask_endpoint_bump (C006 512) = _; rw [consumer006]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link007 : Array.index_usize host_forest.MASK_LINKS 7#usize = ok (11#u16,28#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer007 : P007 11 = 0#u8 := by
  dsimp only [P007, P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer007 : C007 28 = 0#u8 := by
  dsimp only [C007, C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step007 : body s007 = ok (cont s008) := by
  unfold body s007 s008 P008 C008 M008
  have next : Usize.wrapping_add 7#usize 1#usize = 8#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 7#usize (by
      change 8 < Usize.size; simpa using UScalar.hSize (8#usize))
  simpa only [next, show (11#usize).val = 11 from rfl,
    show (28#usize).val = 28 from rfl] using step P007 C007 M007 7#usize 11#usize 28#usize 11#u16 28#u16 1#u8 1#u8
    (by decide) link007 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P007 11) = _; rw [producer007]; rfl) (by change host_forest.mask_endpoint_bump (C007 28) = _; rw [consumer007]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s000 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step000).trans ((run_next _ _ step001).trans ((run_next _ _ step002).trans ((run_next _ _ step003).trans ((run_next _ _ step004).trans ((run_next _ _ step005).trans ((run_next _ _ step006).trans ((run_next _ _ step007).trans (PV_B3_MaskSparse01.suffix))))))))
#print axioms link000
#print axioms producer000
#print axioms consumer000
#print axioms step000
#print axioms link001
#print axioms producer001
#print axioms consumer001
#print axioms step001
#print axioms link002
#print axioms producer002
#print axioms consumer002
#print axioms step002
#print axioms link003
#print axioms producer003
#print axioms consumer003
#print axioms step003
#print axioms link004
#print axioms producer004
#print axioms consumer004
#print axioms step004
#print axioms link005
#print axioms producer005
#print axioms consumer005
#print axioms step005
#print axioms link006
#print axioms producer006
#print axioms consumer006
#print axioms step006
#print axioms link007
#print axioms producer007
#print axioms consumer007
#print axioms step007
#print axioms suffix
end PV_B3_MaskSparse00
