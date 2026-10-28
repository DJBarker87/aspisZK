import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse07
namespace PV_B3_MaskSparse06
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link048 : Array.index_usize host_forest.MASK_LINKS 48#usize = ok (731#u16,748#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer048 : P048 731 = 0#u8 := by
  dsimp only [P048, P047, P046, P045, P044, P043, P042, P041, Function.update]
  dsimp only [P040, P039, P038, P037, P036, P035, P034, P033, Function.update]
  dsimp only [P032, P031, P030, P029, P028, P027, P026, P025, Function.update]
  dsimp only [P024, P023, P022, P021, P020, P019, P018, P017, Function.update]
  dsimp only [P016, P015, P014, P013, P012, P011, P010, P009, Function.update]
  dsimp only [P008, P007, P006, P005, P004, P003, P002, P001, Function.update]
  dsimp only [P000, Function.update]
  rfl
theorem consumer048 : C048 748 = 0#u8 := by
  dsimp only [C048, C047, C046, C045, C044, C043, C042, C041, Function.update]
  dsimp only [C040, C039, C038, C037, C036, C035, C034, C033, Function.update]
  dsimp only [C032, C031, C030, C029, C028, C027, C026, C025, Function.update]
  dsimp only [C024, C023, C022, C021, C020, C019, C018, C017, Function.update]
  dsimp only [C016, C015, C014, C013, C012, C011, C010, C009, Function.update]
  dsimp only [C008, C007, C006, C005, C004, C003, C002, C001, Function.update]
  dsimp only [C000, Function.update]
  rfl
theorem step048 : body s048 = ok (cont s049) := by
  unfold body s048 s049 P049 C049 M049
  have next : Usize.wrapping_add 48#usize 1#usize = 49#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 48#usize (by
      change 49 < Usize.size; simpa using UScalar.hSize (49#usize))
  simpa only [next, show (731#usize).val = 731 from rfl,
    show (748#usize).val = 748 from rfl] using step P048 C048 M048 48#usize 731#usize 748#usize 731#u16 748#u16 1#u8 1#u8
    (by decide) link048 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P048 731) = _; rw [producer048]; rfl) (by change host_forest.mask_endpoint_bump (C048 748) = _; rw [consumer048]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link049 : Array.index_usize host_forest.MASK_LINKS 49#usize = ok (731#u16,736#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer049 : P049 731 = 1#u8 := by
  dsimp only [P049, P048, P047, P046, P045, P044, P043, P042, Function.update]
  dsimp only [P041, P040, P039, P038, P037, P036, P035, P034, Function.update]
  dsimp only [P033, P032, P031, P030, P029, P028, P027, P026, Function.update]
  dsimp only [P025, P024, P023, P022, P021, P020, P019, P018, Function.update]
  dsimp only [P017, P016, P015, P014, P013, P012, P011, P010, Function.update]
  dsimp only [P009, P008, P007, P006, P005, P004, P003, P002, Function.update]
  dsimp only [P001, P000, Function.update]
  rfl
theorem consumer049 : C049 736 = 0#u8 := by
  dsimp only [C049, C048, C047, C046, C045, C044, C043, C042, Function.update]
  dsimp only [C041, C040, C039, C038, C037, C036, C035, C034, Function.update]
  dsimp only [C033, C032, C031, C030, C029, C028, C027, C026, Function.update]
  dsimp only [C025, C024, C023, C022, C021, C020, C019, C018, Function.update]
  dsimp only [C017, C016, C015, C014, C013, C012, C011, C010, Function.update]
  dsimp only [C009, C008, C007, C006, C005, C004, C003, C002, Function.update]
  dsimp only [C001, C000, Function.update]
  rfl
theorem step049 : body s049 = ok (cont s050) := by
  unfold body s049 s050 P050 C050 M050
  have next : Usize.wrapping_add 49#usize 1#usize = 50#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 49#usize (by
      change 50 < Usize.size; simpa using UScalar.hSize (50#usize))
  simpa only [next, show (731#usize).val = 731 from rfl,
    show (736#usize).val = 736 from rfl] using step P049 C049 M049 49#usize 731#usize 736#usize 731#u16 736#u16 2#u8 1#u8
    (by decide) link049 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P049 731) = _; rw [producer049]; rfl) (by change host_forest.mask_endpoint_bump (C049 736) = _; rw [consumer049]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link050 : Array.index_usize host_forest.MASK_LINKS 50#usize = ok (747#u16,764#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer050 : P050 747 = 0#u8 := by
  dsimp only [P050, P049, P048, P047, P046, P045, P044, P043, Function.update]
  dsimp only [P042, P041, P040, P039, P038, P037, P036, P035, Function.update]
  dsimp only [P034, P033, P032, P031, P030, P029, P028, P027, Function.update]
  dsimp only [P026, P025, P024, P023, P022, P021, P020, P019, Function.update]
  dsimp only [P018, P017, P016, P015, P014, P013, P012, P011, Function.update]
  dsimp only [P010, P009, P008, P007, P006, P005, P004, P003, Function.update]
  dsimp only [P002, P001, P000, Function.update]
  rfl
theorem consumer050 : C050 764 = 0#u8 := by
  dsimp only [C050, C049, C048, C047, C046, C045, C044, C043, Function.update]
  dsimp only [C042, C041, C040, C039, C038, C037, C036, C035, Function.update]
  dsimp only [C034, C033, C032, C031, C030, C029, C028, C027, Function.update]
  dsimp only [C026, C025, C024, C023, C022, C021, C020, C019, Function.update]
  dsimp only [C018, C017, C016, C015, C014, C013, C012, C011, Function.update]
  dsimp only [C010, C009, C008, C007, C006, C005, C004, C003, Function.update]
  dsimp only [C002, C001, C000, Function.update]
  rfl
theorem step050 : body s050 = ok (cont s051) := by
  unfold body s050 s051 P051 C051 M051
  have next : Usize.wrapping_add 50#usize 1#usize = 51#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 50#usize (by
      change 51 < Usize.size; simpa using UScalar.hSize (51#usize))
  simpa only [next, show (747#usize).val = 747 from rfl,
    show (764#usize).val = 764 from rfl] using step P050 C050 M050 50#usize 747#usize 764#usize 747#u16 764#u16 1#u8 1#u8
    (by decide) link050 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P050 747) = _; rw [producer050]; rfl) (by change host_forest.mask_endpoint_bump (C050 764) = _; rw [consumer050]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link051 : Array.index_usize host_forest.MASK_LINKS 51#usize = ok (747#u16,752#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer051 : P051 747 = 1#u8 := by
  dsimp only [P051, P050, P049, P048, P047, P046, P045, P044, Function.update]
  dsimp only [P043, P042, P041, P040, P039, P038, P037, P036, Function.update]
  dsimp only [P035, P034, P033, P032, P031, P030, P029, P028, Function.update]
  dsimp only [P027, P026, P025, P024, P023, P022, P021, P020, Function.update]
  dsimp only [P019, P018, P017, P016, P015, P014, P013, P012, Function.update]
  dsimp only [P011, P010, P009, P008, P007, P006, P005, P004, Function.update]
  dsimp only [P003, P002, P001, P000, Function.update]
  rfl
theorem consumer051 : C051 752 = 0#u8 := by
  dsimp only [C051, C050, C049, C048, C047, C046, C045, C044, Function.update]
  dsimp only [C043, C042, C041, C040, C039, C038, C037, C036, Function.update]
  dsimp only [C035, C034, C033, C032, C031, C030, C029, C028, Function.update]
  dsimp only [C027, C026, C025, C024, C023, C022, C021, C020, Function.update]
  dsimp only [C019, C018, C017, C016, C015, C014, C013, C012, Function.update]
  dsimp only [C011, C010, C009, C008, C007, C006, C005, C004, Function.update]
  dsimp only [C003, C002, C001, C000, Function.update]
  rfl
theorem step051 : body s051 = ok (cont s052) := by
  unfold body s051 s052 P052 C052 M052
  have next : Usize.wrapping_add 51#usize 1#usize = 52#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 51#usize (by
      change 52 < Usize.size; simpa using UScalar.hSize (52#usize))
  simpa only [next, show (747#usize).val = 747 from rfl,
    show (752#usize).val = 752 from rfl] using step P051 C051 M051 51#usize 747#usize 752#usize 747#u16 752#u16 2#u8 1#u8
    (by decide) link051 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P051 747) = _; rw [producer051]; rfl) (by change host_forest.mask_endpoint_bump (C051 752) = _; rw [consumer051]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link052 : Array.index_usize host_forest.MASK_LINKS 52#usize = ok (763#u16,780#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer052 : P052 763 = 0#u8 := by
  dsimp only [P052, P051, P050, P049, P048, P047, P046, P045, Function.update]
  dsimp only [P044, P043, P042, P041, P040, P039, P038, P037, Function.update]
  dsimp only [P036, P035, P034, P033, P032, P031, P030, P029, Function.update]
  dsimp only [P028, P027, P026, P025, P024, P023, P022, P021, Function.update]
  dsimp only [P020, P019, P018, P017, P016, P015, P014, P013, Function.update]
  dsimp only [P012, P011, P010, P009, P008, P007, P006, P005, Function.update]
  dsimp only [P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer052 : C052 780 = 0#u8 := by
  dsimp only [C052, C051, C050, C049, C048, C047, C046, C045, Function.update]
  dsimp only [C044, C043, C042, C041, C040, C039, C038, C037, Function.update]
  dsimp only [C036, C035, C034, C033, C032, C031, C030, C029, Function.update]
  dsimp only [C028, C027, C026, C025, C024, C023, C022, C021, Function.update]
  dsimp only [C020, C019, C018, C017, C016, C015, C014, C013, Function.update]
  dsimp only [C012, C011, C010, C009, C008, C007, C006, C005, Function.update]
  dsimp only [C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step052 : body s052 = ok (cont s053) := by
  unfold body s052 s053 P053 C053 M053
  have next : Usize.wrapping_add 52#usize 1#usize = 53#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 52#usize (by
      change 53 < Usize.size; simpa using UScalar.hSize (53#usize))
  simpa only [next, show (763#usize).val = 763 from rfl,
    show (780#usize).val = 780 from rfl] using step P052 C052 M052 52#usize 763#usize 780#usize 763#u16 780#u16 1#u8 1#u8
    (by decide) link052 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P052 763) = _; rw [producer052]; rfl) (by change host_forest.mask_endpoint_bump (C052 780) = _; rw [consumer052]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link053 : Array.index_usize host_forest.MASK_LINKS 53#usize = ok (763#u16,768#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer053 : P053 763 = 1#u8 := by
  dsimp only [P053, P052, P051, P050, P049, P048, P047, P046, Function.update]
  dsimp only [P045, P044, P043, P042, P041, P040, P039, P038, Function.update]
  dsimp only [P037, P036, P035, P034, P033, P032, P031, P030, Function.update]
  dsimp only [P029, P028, P027, P026, P025, P024, P023, P022, Function.update]
  dsimp only [P021, P020, P019, P018, P017, P016, P015, P014, Function.update]
  dsimp only [P013, P012, P011, P010, P009, P008, P007, P006, Function.update]
  dsimp only [P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer053 : C053 768 = 0#u8 := by
  dsimp only [C053, C052, C051, C050, C049, C048, C047, C046, Function.update]
  dsimp only [C045, C044, C043, C042, C041, C040, C039, C038, Function.update]
  dsimp only [C037, C036, C035, C034, C033, C032, C031, C030, Function.update]
  dsimp only [C029, C028, C027, C026, C025, C024, C023, C022, Function.update]
  dsimp only [C021, C020, C019, C018, C017, C016, C015, C014, Function.update]
  dsimp only [C013, C012, C011, C010, C009, C008, C007, C006, Function.update]
  dsimp only [C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step053 : body s053 = ok (cont s054) := by
  unfold body s053 s054 P054 C054 M054
  have next : Usize.wrapping_add 53#usize 1#usize = 54#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 53#usize (by
      change 54 < Usize.size; simpa using UScalar.hSize (54#usize))
  simpa only [next, show (763#usize).val = 763 from rfl,
    show (768#usize).val = 768 from rfl] using step P053 C053 M053 53#usize 763#usize 768#usize 763#u16 768#u16 2#u8 1#u8
    (by decide) link053 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P053 763) = _; rw [producer053]; rfl) (by change host_forest.mask_endpoint_bump (C053 768) = _; rw [consumer053]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link054 : Array.index_usize host_forest.MASK_LINKS 54#usize = ok (779#u16,796#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer054 : P054 779 = 0#u8 := by
  dsimp only [P054, P053, P052, P051, P050, P049, P048, P047, Function.update]
  dsimp only [P046, P045, P044, P043, P042, P041, P040, P039, Function.update]
  dsimp only [P038, P037, P036, P035, P034, P033, P032, P031, Function.update]
  dsimp only [P030, P029, P028, P027, P026, P025, P024, P023, Function.update]
  dsimp only [P022, P021, P020, P019, P018, P017, P016, P015, Function.update]
  dsimp only [P014, P013, P012, P011, P010, P009, P008, P007, Function.update]
  dsimp only [P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer054 : C054 796 = 0#u8 := by
  dsimp only [C054, C053, C052, C051, C050, C049, C048, C047, Function.update]
  dsimp only [C046, C045, C044, C043, C042, C041, C040, C039, Function.update]
  dsimp only [C038, C037, C036, C035, C034, C033, C032, C031, Function.update]
  dsimp only [C030, C029, C028, C027, C026, C025, C024, C023, Function.update]
  dsimp only [C022, C021, C020, C019, C018, C017, C016, C015, Function.update]
  dsimp only [C014, C013, C012, C011, C010, C009, C008, C007, Function.update]
  dsimp only [C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step054 : body s054 = ok (cont s055) := by
  unfold body s054 s055 P055 C055 M055
  have next : Usize.wrapping_add 54#usize 1#usize = 55#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 54#usize (by
      change 55 < Usize.size; simpa using UScalar.hSize (55#usize))
  simpa only [next, show (779#usize).val = 779 from rfl,
    show (796#usize).val = 796 from rfl] using step P054 C054 M054 54#usize 779#usize 796#usize 779#u16 796#u16 1#u8 1#u8
    (by decide) link054 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P054 779) = _; rw [producer054]; rfl) (by change host_forest.mask_endpoint_bump (C054 796) = _; rw [consumer054]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link055 : Array.index_usize host_forest.MASK_LINKS 55#usize = ok (779#u16,784#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer055 : P055 779 = 1#u8 := by
  dsimp only [P055, P054, P053, P052, P051, P050, P049, P048, Function.update]
  dsimp only [P047, P046, P045, P044, P043, P042, P041, P040, Function.update]
  dsimp only [P039, P038, P037, P036, P035, P034, P033, P032, Function.update]
  dsimp only [P031, P030, P029, P028, P027, P026, P025, P024, Function.update]
  dsimp only [P023, P022, P021, P020, P019, P018, P017, P016, Function.update]
  dsimp only [P015, P014, P013, P012, P011, P010, P009, P008, Function.update]
  dsimp only [P007, P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer055 : C055 784 = 0#u8 := by
  dsimp only [C055, C054, C053, C052, C051, C050, C049, C048, Function.update]
  dsimp only [C047, C046, C045, C044, C043, C042, C041, C040, Function.update]
  dsimp only [C039, C038, C037, C036, C035, C034, C033, C032, Function.update]
  dsimp only [C031, C030, C029, C028, C027, C026, C025, C024, Function.update]
  dsimp only [C023, C022, C021, C020, C019, C018, C017, C016, Function.update]
  dsimp only [C015, C014, C013, C012, C011, C010, C009, C008, Function.update]
  dsimp only [C007, C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step055 : body s055 = ok (cont s056) := by
  unfold body s055 s056 P056 C056 M056
  have next : Usize.wrapping_add 55#usize 1#usize = 56#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 55#usize (by
      change 56 < Usize.size; simpa using UScalar.hSize (56#usize))
  simpa only [next, show (779#usize).val = 779 from rfl,
    show (784#usize).val = 784 from rfl] using step P055 C055 M055 55#usize 779#usize 784#usize 779#u16 784#u16 2#u8 1#u8
    (by decide) link055 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P055 779) = _; rw [producer055]; rfl) (by change host_forest.mask_endpoint_bump (C055 784) = _; rw [consumer055]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s048 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step048).trans ((run_next _ _ step049).trans ((run_next _ _ step050).trans ((run_next _ _ step051).trans ((run_next _ _ step052).trans ((run_next _ _ step053).trans ((run_next _ _ step054).trans ((run_next _ _ step055).trans (PV_B3_MaskSparse07.suffix))))))))
#print axioms link048
#print axioms producer048
#print axioms consumer048
#print axioms step048
#print axioms link049
#print axioms producer049
#print axioms consumer049
#print axioms step049
#print axioms link050
#print axioms producer050
#print axioms consumer050
#print axioms step050
#print axioms link051
#print axioms producer051
#print axioms consumer051
#print axioms step051
#print axioms link052
#print axioms producer052
#print axioms consumer052
#print axioms step052
#print axioms link053
#print axioms producer053
#print axioms consumer053
#print axioms step053
#print axioms link054
#print axioms producer054
#print axioms consumer054
#print axioms step054
#print axioms link055
#print axioms producer055
#print axioms consumer055
#print axioms step055
#print axioms suffix
end PV_B3_MaskSparse06
