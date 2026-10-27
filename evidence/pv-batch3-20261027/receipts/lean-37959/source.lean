import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse08
namespace PV_B3_MaskSparse07
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link056 : Array.index_usize host_forest.MASK_LINKS 56#usize = ok (795#u16,812#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer056 : P056 795 = 0#u8 := by
  dsimp only [P056, P055, P054, P053, P052, P051, P050, P049, Function.update]
  dsimp only [P048, P047, P046, P045, P044, P043, P042, P041, Function.update]
  dsimp only [P040, P039, P038, P037, P036, P035, P034, P033, Function.update]
  dsimp only [P032, P031, P030, P029, P028, P027, P026, P025, Function.update]
  dsimp only [P024, P023, P022, P021, P020, P019, P018, P017, Function.update]
  dsimp only [P016, P015, P014, P013, P012, P011, P010, P009, Function.update]
  dsimp only [P008, P007, P006, P005, P004, P003, P002, P001, Function.update]
  dsimp only [P000, Function.update]
  rfl
theorem consumer056 : C056 812 = 0#u8 := by
  dsimp only [C056, C055, C054, C053, C052, C051, C050, C049, Function.update]
  dsimp only [C048, C047, C046, C045, C044, C043, C042, C041, Function.update]
  dsimp only [C040, C039, C038, C037, C036, C035, C034, C033, Function.update]
  dsimp only [C032, C031, C030, C029, C028, C027, C026, C025, Function.update]
  dsimp only [C024, C023, C022, C021, C020, C019, C018, C017, Function.update]
  dsimp only [C016, C015, C014, C013, C012, C011, C010, C009, Function.update]
  dsimp only [C008, C007, C006, C005, C004, C003, C002, C001, Function.update]
  dsimp only [C000, Function.update]
  rfl
theorem step056 : body s056 = ok (cont s057) := by
  unfold body s056 s057 P057 C057 M057
  have next : Usize.wrapping_add 56#usize 1#usize = 57#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 56#usize (by
      change 57 < Usize.size; simpa using UScalar.hSize (57#usize))
  simpa only [next, show (795#usize).val = 795 from rfl,
    show (812#usize).val = 812 from rfl] using step P056 C056 M056 56#usize 795#usize 812#usize 795#u16 812#u16 1#u8 1#u8
    (by decide) link056 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P056 795) = _; rw [producer056]; rfl) (by change host_forest.mask_endpoint_bump (C056 812) = _; rw [consumer056]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link057 : Array.index_usize host_forest.MASK_LINKS 57#usize = ok (795#u16,800#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer057 : P057 795 = 1#u8 := by
  dsimp only [P057, P056, P055, P054, P053, P052, P051, P050, Function.update]
  dsimp only [P049, P048, P047, P046, P045, P044, P043, P042, Function.update]
  dsimp only [P041, P040, P039, P038, P037, P036, P035, P034, Function.update]
  dsimp only [P033, P032, P031, P030, P029, P028, P027, P026, Function.update]
  dsimp only [P025, P024, P023, P022, P021, P020, P019, P018, Function.update]
  dsimp only [P017, P016, P015, P014, P013, P012, P011, P010, Function.update]
  dsimp only [P009, P008, P007, P006, P005, P004, P003, P002, Function.update]
  dsimp only [P001, P000, Function.update]
  rfl
theorem consumer057 : C057 800 = 0#u8 := by
  dsimp only [C057, C056, C055, C054, C053, C052, C051, C050, Function.update]
  dsimp only [C049, C048, C047, C046, C045, C044, C043, C042, Function.update]
  dsimp only [C041, C040, C039, C038, C037, C036, C035, C034, Function.update]
  dsimp only [C033, C032, C031, C030, C029, C028, C027, C026, Function.update]
  dsimp only [C025, C024, C023, C022, C021, C020, C019, C018, Function.update]
  dsimp only [C017, C016, C015, C014, C013, C012, C011, C010, Function.update]
  dsimp only [C009, C008, C007, C006, C005, C004, C003, C002, Function.update]
  dsimp only [C001, C000, Function.update]
  rfl
theorem step057 : body s057 = ok (cont s058) := by
  unfold body s057 s058 P058 C058 M058
  have next : Usize.wrapping_add 57#usize 1#usize = 58#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 57#usize (by
      change 58 < Usize.size; simpa using UScalar.hSize (58#usize))
  simpa only [next, show (795#usize).val = 795 from rfl,
    show (800#usize).val = 800 from rfl] using step P057 C057 M057 57#usize 795#usize 800#usize 795#u16 800#u16 2#u8 1#u8
    (by decide) link057 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P057 795) = _; rw [producer057]; rfl) (by change host_forest.mask_endpoint_bump (C057 800) = _; rw [consumer057]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link058 : Array.index_usize host_forest.MASK_LINKS 58#usize = ok (811#u16,828#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer058 : P058 811 = 0#u8 := by
  dsimp only [P058, P057, P056, P055, P054, P053, P052, P051, Function.update]
  dsimp only [P050, P049, P048, P047, P046, P045, P044, P043, Function.update]
  dsimp only [P042, P041, P040, P039, P038, P037, P036, P035, Function.update]
  dsimp only [P034, P033, P032, P031, P030, P029, P028, P027, Function.update]
  dsimp only [P026, P025, P024, P023, P022, P021, P020, P019, Function.update]
  dsimp only [P018, P017, P016, P015, P014, P013, P012, P011, Function.update]
  dsimp only [P010, P009, P008, P007, P006, P005, P004, P003, Function.update]
  dsimp only [P002, P001, P000, Function.update]
  rfl
theorem consumer058 : C058 828 = 0#u8 := by
  dsimp only [C058, C057, C056, C055, C054, C053, C052, C051, Function.update]
  dsimp only [C050, C049, C048, C047, C046, C045, C044, C043, Function.update]
  dsimp only [C042, C041, C040, C039, C038, C037, C036, C035, Function.update]
  dsimp only [C034, C033, C032, C031, C030, C029, C028, C027, Function.update]
  dsimp only [C026, C025, C024, C023, C022, C021, C020, C019, Function.update]
  dsimp only [C018, C017, C016, C015, C014, C013, C012, C011, Function.update]
  dsimp only [C010, C009, C008, C007, C006, C005, C004, C003, Function.update]
  dsimp only [C002, C001, C000, Function.update]
  rfl
theorem step058 : body s058 = ok (cont s059) := by
  unfold body s058 s059 P059 C059 M059
  have next : Usize.wrapping_add 58#usize 1#usize = 59#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 58#usize (by
      change 59 < Usize.size; simpa using UScalar.hSize (59#usize))
  simpa only [next, show (811#usize).val = 811 from rfl,
    show (828#usize).val = 828 from rfl] using step P058 C058 M058 58#usize 811#usize 828#usize 811#u16 828#u16 1#u8 1#u8
    (by decide) link058 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P058 811) = _; rw [producer058]; rfl) (by change host_forest.mask_endpoint_bump (C058 828) = _; rw [consumer058]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link059 : Array.index_usize host_forest.MASK_LINKS 59#usize = ok (811#u16,816#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer059 : P059 811 = 1#u8 := by
  dsimp only [P059, P058, P057, P056, P055, P054, P053, P052, Function.update]
  dsimp only [P051, P050, P049, P048, P047, P046, P045, P044, Function.update]
  dsimp only [P043, P042, P041, P040, P039, P038, P037, P036, Function.update]
  dsimp only [P035, P034, P033, P032, P031, P030, P029, P028, Function.update]
  dsimp only [P027, P026, P025, P024, P023, P022, P021, P020, Function.update]
  dsimp only [P019, P018, P017, P016, P015, P014, P013, P012, Function.update]
  dsimp only [P011, P010, P009, P008, P007, P006, P005, P004, Function.update]
  dsimp only [P003, P002, P001, P000, Function.update]
  rfl
theorem consumer059 : C059 816 = 0#u8 := by
  dsimp only [C059, C058, C057, C056, C055, C054, C053, C052, Function.update]
  dsimp only [C051, C050, C049, C048, C047, C046, C045, C044, Function.update]
  dsimp only [C043, C042, C041, C040, C039, C038, C037, C036, Function.update]
  dsimp only [C035, C034, C033, C032, C031, C030, C029, C028, Function.update]
  dsimp only [C027, C026, C025, C024, C023, C022, C021, C020, Function.update]
  dsimp only [C019, C018, C017, C016, C015, C014, C013, C012, Function.update]
  dsimp only [C011, C010, C009, C008, C007, C006, C005, C004, Function.update]
  dsimp only [C003, C002, C001, C000, Function.update]
  rfl
theorem step059 : body s059 = ok (cont s060) := by
  unfold body s059 s060 P060 C060 M060
  have next : Usize.wrapping_add 59#usize 1#usize = 60#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 59#usize (by
      change 60 < Usize.size; simpa using UScalar.hSize (60#usize))
  simpa only [next, show (811#usize).val = 811 from rfl,
    show (816#usize).val = 816 from rfl] using step P059 C059 M059 59#usize 811#usize 816#usize 811#u16 816#u16 2#u8 1#u8
    (by decide) link059 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P059 811) = _; rw [producer059]; rfl) (by change host_forest.mask_endpoint_bump (C059 816) = _; rw [consumer059]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link060 : Array.index_usize host_forest.MASK_LINKS 60#usize = ok (827#u16,844#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer060 : P060 827 = 0#u8 := by
  dsimp only [P060, P059, P058, P057, P056, P055, P054, P053, Function.update]
  dsimp only [P052, P051, P050, P049, P048, P047, P046, P045, Function.update]
  dsimp only [P044, P043, P042, P041, P040, P039, P038, P037, Function.update]
  dsimp only [P036, P035, P034, P033, P032, P031, P030, P029, Function.update]
  dsimp only [P028, P027, P026, P025, P024, P023, P022, P021, Function.update]
  dsimp only [P020, P019, P018, P017, P016, P015, P014, P013, Function.update]
  dsimp only [P012, P011, P010, P009, P008, P007, P006, P005, Function.update]
  dsimp only [P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer060 : C060 844 = 0#u8 := by
  dsimp only [C060, C059, C058, C057, C056, C055, C054, C053, Function.update]
  dsimp only [C052, C051, C050, C049, C048, C047, C046, C045, Function.update]
  dsimp only [C044, C043, C042, C041, C040, C039, C038, C037, Function.update]
  dsimp only [C036, C035, C034, C033, C032, C031, C030, C029, Function.update]
  dsimp only [C028, C027, C026, C025, C024, C023, C022, C021, Function.update]
  dsimp only [C020, C019, C018, C017, C016, C015, C014, C013, Function.update]
  dsimp only [C012, C011, C010, C009, C008, C007, C006, C005, Function.update]
  dsimp only [C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step060 : body s060 = ok (cont s061) := by
  unfold body s060 s061 P061 C061 M061
  have next : Usize.wrapping_add 60#usize 1#usize = 61#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 60#usize (by
      change 61 < Usize.size; simpa using UScalar.hSize (61#usize))
  simpa only [next, show (827#usize).val = 827 from rfl,
    show (844#usize).val = 844 from rfl] using step P060 C060 M060 60#usize 827#usize 844#usize 827#u16 844#u16 1#u8 1#u8
    (by decide) link060 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P060 827) = _; rw [producer060]; rfl) (by change host_forest.mask_endpoint_bump (C060 844) = _; rw [consumer060]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link061 : Array.index_usize host_forest.MASK_LINKS 61#usize = ok (827#u16,832#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer061 : P061 827 = 1#u8 := by
  dsimp only [P061, P060, P059, P058, P057, P056, P055, P054, Function.update]
  dsimp only [P053, P052, P051, P050, P049, P048, P047, P046, Function.update]
  dsimp only [P045, P044, P043, P042, P041, P040, P039, P038, Function.update]
  dsimp only [P037, P036, P035, P034, P033, P032, P031, P030, Function.update]
  dsimp only [P029, P028, P027, P026, P025, P024, P023, P022, Function.update]
  dsimp only [P021, P020, P019, P018, P017, P016, P015, P014, Function.update]
  dsimp only [P013, P012, P011, P010, P009, P008, P007, P006, Function.update]
  dsimp only [P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer061 : C061 832 = 0#u8 := by
  dsimp only [C061, C060, C059, C058, C057, C056, C055, C054, Function.update]
  dsimp only [C053, C052, C051, C050, C049, C048, C047, C046, Function.update]
  dsimp only [C045, C044, C043, C042, C041, C040, C039, C038, Function.update]
  dsimp only [C037, C036, C035, C034, C033, C032, C031, C030, Function.update]
  dsimp only [C029, C028, C027, C026, C025, C024, C023, C022, Function.update]
  dsimp only [C021, C020, C019, C018, C017, C016, C015, C014, Function.update]
  dsimp only [C013, C012, C011, C010, C009, C008, C007, C006, Function.update]
  dsimp only [C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step061 : body s061 = ok (cont s062) := by
  unfold body s061 s062 P062 C062 M062
  have next : Usize.wrapping_add 61#usize 1#usize = 62#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 61#usize (by
      change 62 < Usize.size; simpa using UScalar.hSize (62#usize))
  simpa only [next, show (827#usize).val = 827 from rfl,
    show (832#usize).val = 832 from rfl] using step P061 C061 M061 61#usize 827#usize 832#usize 827#u16 832#u16 2#u8 1#u8
    (by decide) link061 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P061 827) = _; rw [producer061]; rfl) (by change host_forest.mask_endpoint_bump (C061 832) = _; rw [consumer061]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link062 : Array.index_usize host_forest.MASK_LINKS 62#usize = ok (843#u16,860#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer062 : P062 843 = 0#u8 := by
  dsimp only [P062, P061, P060, P059, P058, P057, P056, P055, Function.update]
  dsimp only [P054, P053, P052, P051, P050, P049, P048, P047, Function.update]
  dsimp only [P046, P045, P044, P043, P042, P041, P040, P039, Function.update]
  dsimp only [P038, P037, P036, P035, P034, P033, P032, P031, Function.update]
  dsimp only [P030, P029, P028, P027, P026, P025, P024, P023, Function.update]
  dsimp only [P022, P021, P020, P019, P018, P017, P016, P015, Function.update]
  dsimp only [P014, P013, P012, P011, P010, P009, P008, P007, Function.update]
  dsimp only [P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer062 : C062 860 = 0#u8 := by
  dsimp only [C062, C061, C060, C059, C058, C057, C056, C055, Function.update]
  dsimp only [C054, C053, C052, C051, C050, C049, C048, C047, Function.update]
  dsimp only [C046, C045, C044, C043, C042, C041, C040, C039, Function.update]
  dsimp only [C038, C037, C036, C035, C034, C033, C032, C031, Function.update]
  dsimp only [C030, C029, C028, C027, C026, C025, C024, C023, Function.update]
  dsimp only [C022, C021, C020, C019, C018, C017, C016, C015, Function.update]
  dsimp only [C014, C013, C012, C011, C010, C009, C008, C007, Function.update]
  dsimp only [C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step062 : body s062 = ok (cont s063) := by
  unfold body s062 s063 P063 C063 M063
  have next : Usize.wrapping_add 62#usize 1#usize = 63#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 62#usize (by
      change 63 < Usize.size; simpa using UScalar.hSize (63#usize))
  simpa only [next, show (843#usize).val = 843 from rfl,
    show (860#usize).val = 860 from rfl] using step P062 C062 M062 62#usize 843#usize 860#usize 843#u16 860#u16 1#u8 1#u8
    (by decide) link062 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P062 843) = _; rw [producer062]; rfl) (by change host_forest.mask_endpoint_bump (C062 860) = _; rw [consumer062]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link063 : Array.index_usize host_forest.MASK_LINKS 63#usize = ok (843#u16,848#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer063 : P063 843 = 1#u8 := by
  dsimp only [P063, P062, P061, P060, P059, P058, P057, P056, Function.update]
  dsimp only [P055, P054, P053, P052, P051, P050, P049, P048, Function.update]
  dsimp only [P047, P046, P045, P044, P043, P042, P041, P040, Function.update]
  dsimp only [P039, P038, P037, P036, P035, P034, P033, P032, Function.update]
  dsimp only [P031, P030, P029, P028, P027, P026, P025, P024, Function.update]
  dsimp only [P023, P022, P021, P020, P019, P018, P017, P016, Function.update]
  dsimp only [P015, P014, P013, P012, P011, P010, P009, P008, Function.update]
  dsimp only [P007, P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer063 : C063 848 = 0#u8 := by
  dsimp only [C063, C062, C061, C060, C059, C058, C057, C056, Function.update]
  dsimp only [C055, C054, C053, C052, C051, C050, C049, C048, Function.update]
  dsimp only [C047, C046, C045, C044, C043, C042, C041, C040, Function.update]
  dsimp only [C039, C038, C037, C036, C035, C034, C033, C032, Function.update]
  dsimp only [C031, C030, C029, C028, C027, C026, C025, C024, Function.update]
  dsimp only [C023, C022, C021, C020, C019, C018, C017, C016, Function.update]
  dsimp only [C015, C014, C013, C012, C011, C010, C009, C008, Function.update]
  dsimp only [C007, C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step063 : body s063 = ok (cont s064) := by
  unfold body s063 s064 P064 C064 M064
  have next : Usize.wrapping_add 63#usize 1#usize = 64#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 63#usize (by
      change 64 < Usize.size; simpa using UScalar.hSize (64#usize))
  simpa only [next, show (843#usize).val = 843 from rfl,
    show (848#usize).val = 848 from rfl] using step P063 C063 M063 63#usize 843#usize 848#usize 843#u16 848#u16 2#u8 1#u8
    (by decide) link063 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P063 843) = _; rw [producer063]; rfl) (by change host_forest.mask_endpoint_bump (C063 848) = _; rw [consumer063]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s056 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step056).trans ((run_next _ _ step057).trans ((run_next _ _ step058).trans ((run_next _ _ step059).trans ((run_next _ _ step060).trans ((run_next _ _ step061).trans ((run_next _ _ step062).trans ((run_next _ _ step063).trans (PV_B3_MaskSparse08.suffix))))))))
#print axioms link056
#print axioms producer056
#print axioms consumer056
#print axioms step056
#print axioms link057
#print axioms producer057
#print axioms consumer057
#print axioms step057
#print axioms link058
#print axioms producer058
#print axioms consumer058
#print axioms step058
#print axioms link059
#print axioms producer059
#print axioms consumer059
#print axioms step059
#print axioms link060
#print axioms producer060
#print axioms consumer060
#print axioms step060
#print axioms link061
#print axioms producer061
#print axioms consumer061
#print axioms step061
#print axioms link062
#print axioms producer062
#print axioms consumer062
#print axioms step062
#print axioms link063
#print axioms producer063
#print axioms consumer063
#print axioms step063
#print axioms suffix
end PV_B3_MaskSparse07
