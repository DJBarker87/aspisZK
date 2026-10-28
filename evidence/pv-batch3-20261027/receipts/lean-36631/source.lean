import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse13
namespace PV_B3_MaskSparse12
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link096 : Array.index_usize host_forest.MASK_LINKS 96#usize = ok (954#u16,224#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer096 : P096 954 = 1#u8 := by
  dsimp only [P096, P095, P094, P093, P092, P091, P090, P089, Function.update]
  dsimp only [P088, P087, P086, P085, P084, P083, P082, P081, Function.update]
  dsimp only [P080, P079, P078, P077, P076, P075, P074, P073, Function.update]
  dsimp only [P072, P071, P070, P069, P068, P067, P066, P065, Function.update]
  dsimp only [P064, P063, P062, P061, P060, P059, P058, P057, Function.update]
  dsimp only [P056, P055, P054, P053, P052, P051, P050, P049, Function.update]
  dsimp only [P048, P047, P046, P045, P044, P043, P042, P041, Function.update]
  dsimp only [P040, P039, P038, P037, P036, P035, P034, P033, Function.update]
  dsimp only [P032, P031, P030, P029, P028, P027, P026, P025, Function.update]
  dsimp only [P024, P023, P022, P021, P020, P019, P018, P017, Function.update]
  dsimp only [P016, P015, P014, P013, P012, P011, P010, P009, Function.update]
  dsimp only [P008, P007, P006, P005, P004, P003, P002, P001, Function.update]
  dsimp only [P000, Function.update]
  rfl
theorem consumer096 : C096 224 = 0#u8 := by
  dsimp only [C096, C095, C094, C093, C092, C091, C090, C089, Function.update]
  dsimp only [C088, C087, C086, C085, C084, C083, C082, C081, Function.update]
  dsimp only [C080, C079, C078, C077, C076, C075, C074, C073, Function.update]
  dsimp only [C072, C071, C070, C069, C068, C067, C066, C065, Function.update]
  dsimp only [C064, C063, C062, C061, C060, C059, C058, C057, Function.update]
  dsimp only [C056, C055, C054, C053, C052, C051, C050, C049, Function.update]
  dsimp only [C048, C047, C046, C045, C044, C043, C042, C041, Function.update]
  dsimp only [C040, C039, C038, C037, C036, C035, C034, C033, Function.update]
  dsimp only [C032, C031, C030, C029, C028, C027, C026, C025, Function.update]
  dsimp only [C024, C023, C022, C021, C020, C019, C018, C017, Function.update]
  dsimp only [C016, C015, C014, C013, C012, C011, C010, C009, Function.update]
  dsimp only [C008, C007, C006, C005, C004, C003, C002, C001, Function.update]
  dsimp only [C000, Function.update]
  rfl
theorem step096 : body s096 = ok (cont s097) := by
  unfold body s096 s097 P097 C097 M097
  have next : Usize.wrapping_add 96#usize 1#usize = 97#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 96#usize (by
      change 97 < Usize.size; simpa using UScalar.hSize (97#usize))
  simpa only [next, show (954#usize).val = 954 from rfl,
    show (224#usize).val = 224 from rfl] using step P096 C096 M096 96#usize 954#usize 224#usize 954#u16 224#u16 2#u8 1#u8
    (by decide) link096 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P096 954) = _; rw [producer096]; rfl) (by change host_forest.mask_endpoint_bump (C096 224) = _; rw [consumer096]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link097 : Array.index_usize host_forest.MASK_LINKS 97#usize = ok (235#u16,957#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer097 : P097 235 = 0#u8 := by
  dsimp only [P097, P096, P095, P094, P093, P092, P091, P090, Function.update]
  dsimp only [P089, P088, P087, P086, P085, P084, P083, P082, Function.update]
  dsimp only [P081, P080, P079, P078, P077, P076, P075, P074, Function.update]
  dsimp only [P073, P072, P071, P070, P069, P068, P067, P066, Function.update]
  dsimp only [P065, P064, P063, P062, P061, P060, P059, P058, Function.update]
  dsimp only [P057, P056, P055, P054, P053, P052, P051, P050, Function.update]
  dsimp only [P049, P048, P047, P046, P045, P044, P043, P042, Function.update]
  dsimp only [P041, P040, P039, P038, P037, P036, P035, P034, Function.update]
  dsimp only [P033, P032, P031, P030, P029, P028, P027, P026, Function.update]
  dsimp only [P025, P024, P023, P022, P021, P020, P019, P018, Function.update]
  dsimp only [P017, P016, P015, P014, P013, P012, P011, P010, Function.update]
  dsimp only [P009, P008, P007, P006, P005, P004, P003, P002, Function.update]
  dsimp only [P001, P000, Function.update]
  rfl
theorem consumer097 : C097 957 = 0#u8 := by
  dsimp only [C097, C096, C095, C094, C093, C092, C091, C090, Function.update]
  dsimp only [C089, C088, C087, C086, C085, C084, C083, C082, Function.update]
  dsimp only [C081, C080, C079, C078, C077, C076, C075, C074, Function.update]
  dsimp only [C073, C072, C071, C070, C069, C068, C067, C066, Function.update]
  dsimp only [C065, C064, C063, C062, C061, C060, C059, C058, Function.update]
  dsimp only [C057, C056, C055, C054, C053, C052, C051, C050, Function.update]
  dsimp only [C049, C048, C047, C046, C045, C044, C043, C042, Function.update]
  dsimp only [C041, C040, C039, C038, C037, C036, C035, C034, Function.update]
  dsimp only [C033, C032, C031, C030, C029, C028, C027, C026, Function.update]
  dsimp only [C025, C024, C023, C022, C021, C020, C019, C018, Function.update]
  dsimp only [C017, C016, C015, C014, C013, C012, C011, C010, Function.update]
  dsimp only [C009, C008, C007, C006, C005, C004, C003, C002, Function.update]
  dsimp only [C001, C000, Function.update]
  rfl
theorem step097 : body s097 = ok (cont s098) := by
  unfold body s097 s098 P098 C098 M098
  have next : Usize.wrapping_add 97#usize 1#usize = 98#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 97#usize (by
      change 98 < Usize.size; simpa using UScalar.hSize (98#usize))
  simpa only [next, show (235#usize).val = 235 from rfl,
    show (957#usize).val = 957 from rfl] using step P097 C097 M097 97#usize 235#usize 957#usize 235#u16 957#u16 1#u8 1#u8
    (by decide) link097 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P097 235) = _; rw [producer097]; rfl) (by change host_forest.mask_endpoint_bump (C097 957) = _; rw [consumer097]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link098 : Array.index_usize host_forest.MASK_LINKS 98#usize = ok (958#u16,252#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer098 : P098 958 = 0#u8 := by
  dsimp only [P098, P097, P096, P095, P094, P093, P092, P091, Function.update]
  dsimp only [P090, P089, P088, P087, P086, P085, P084, P083, Function.update]
  dsimp only [P082, P081, P080, P079, P078, P077, P076, P075, Function.update]
  dsimp only [P074, P073, P072, P071, P070, P069, P068, P067, Function.update]
  dsimp only [P066, P065, P064, P063, P062, P061, P060, P059, Function.update]
  dsimp only [P058, P057, P056, P055, P054, P053, P052, P051, Function.update]
  dsimp only [P050, P049, P048, P047, P046, P045, P044, P043, Function.update]
  dsimp only [P042, P041, P040, P039, P038, P037, P036, P035, Function.update]
  dsimp only [P034, P033, P032, P031, P030, P029, P028, P027, Function.update]
  dsimp only [P026, P025, P024, P023, P022, P021, P020, P019, Function.update]
  dsimp only [P018, P017, P016, P015, P014, P013, P012, P011, Function.update]
  dsimp only [P010, P009, P008, P007, P006, P005, P004, P003, Function.update]
  dsimp only [P002, P001, P000, Function.update]
  rfl
theorem consumer098 : C098 252 = 0#u8 := by
  dsimp only [C098, C097, C096, C095, C094, C093, C092, C091, Function.update]
  dsimp only [C090, C089, C088, C087, C086, C085, C084, C083, Function.update]
  dsimp only [C082, C081, C080, C079, C078, C077, C076, C075, Function.update]
  dsimp only [C074, C073, C072, C071, C070, C069, C068, C067, Function.update]
  dsimp only [C066, C065, C064, C063, C062, C061, C060, C059, Function.update]
  dsimp only [C058, C057, C056, C055, C054, C053, C052, C051, Function.update]
  dsimp only [C050, C049, C048, C047, C046, C045, C044, C043, Function.update]
  dsimp only [C042, C041, C040, C039, C038, C037, C036, C035, Function.update]
  dsimp only [C034, C033, C032, C031, C030, C029, C028, C027, Function.update]
  dsimp only [C026, C025, C024, C023, C022, C021, C020, C019, Function.update]
  dsimp only [C018, C017, C016, C015, C014, C013, C012, C011, Function.update]
  dsimp only [C010, C009, C008, C007, C006, C005, C004, C003, Function.update]
  dsimp only [C002, C001, C000, Function.update]
  rfl
theorem step098 : body s098 = ok (cont s099) := by
  unfold body s098 s099 P099 C099 M099
  have next : Usize.wrapping_add 98#usize 1#usize = 99#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 98#usize (by
      change 99 < Usize.size; simpa using UScalar.hSize (99#usize))
  simpa only [next, show (958#usize).val = 958 from rfl,
    show (252#usize).val = 252 from rfl] using step P098 C098 M098 98#usize 958#usize 252#usize 958#u16 252#u16 1#u8 1#u8
    (by decide) link098 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P098 958) = _; rw [producer098]; rfl) (by change host_forest.mask_endpoint_bump (C098 252) = _; rw [consumer098]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link099 : Array.index_usize host_forest.MASK_LINKS 99#usize = ok (958#u16,240#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer099 : P099 958 = 1#u8 := by
  dsimp only [P099, P098, P097, P096, P095, P094, P093, P092, Function.update]
  dsimp only [P091, P090, P089, P088, P087, P086, P085, P084, Function.update]
  dsimp only [P083, P082, P081, P080, P079, P078, P077, P076, Function.update]
  dsimp only [P075, P074, P073, P072, P071, P070, P069, P068, Function.update]
  dsimp only [P067, P066, P065, P064, P063, P062, P061, P060, Function.update]
  dsimp only [P059, P058, P057, P056, P055, P054, P053, P052, Function.update]
  dsimp only [P051, P050, P049, P048, P047, P046, P045, P044, Function.update]
  dsimp only [P043, P042, P041, P040, P039, P038, P037, P036, Function.update]
  dsimp only [P035, P034, P033, P032, P031, P030, P029, P028, Function.update]
  dsimp only [P027, P026, P025, P024, P023, P022, P021, P020, Function.update]
  dsimp only [P019, P018, P017, P016, P015, P014, P013, P012, Function.update]
  dsimp only [P011, P010, P009, P008, P007, P006, P005, P004, Function.update]
  dsimp only [P003, P002, P001, P000, Function.update]
  rfl
theorem consumer099 : C099 240 = 0#u8 := by
  dsimp only [C099, C098, C097, C096, C095, C094, C093, C092, Function.update]
  dsimp only [C091, C090, C089, C088, C087, C086, C085, C084, Function.update]
  dsimp only [C083, C082, C081, C080, C079, C078, C077, C076, Function.update]
  dsimp only [C075, C074, C073, C072, C071, C070, C069, C068, Function.update]
  dsimp only [C067, C066, C065, C064, C063, C062, C061, C060, Function.update]
  dsimp only [C059, C058, C057, C056, C055, C054, C053, C052, Function.update]
  dsimp only [C051, C050, C049, C048, C047, C046, C045, C044, Function.update]
  dsimp only [C043, C042, C041, C040, C039, C038, C037, C036, Function.update]
  dsimp only [C035, C034, C033, C032, C031, C030, C029, C028, Function.update]
  dsimp only [C027, C026, C025, C024, C023, C022, C021, C020, Function.update]
  dsimp only [C019, C018, C017, C016, C015, C014, C013, C012, Function.update]
  dsimp only [C011, C010, C009, C008, C007, C006, C005, C004, Function.update]
  dsimp only [C003, C002, C001, C000, Function.update]
  rfl
theorem step099 : body s099 = ok (cont s100) := by
  unfold body s099 s100 P100 C100 M100
  have next : Usize.wrapping_add 99#usize 1#usize = 100#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 99#usize (by
      change 100 < Usize.size; simpa using UScalar.hSize (100#usize))
  simpa only [next, show (958#usize).val = 958 from rfl,
    show (240#usize).val = 240 from rfl] using step P099 C099 M099 99#usize 958#usize 240#usize 958#u16 240#u16 2#u8 1#u8
    (by decide) link099 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P099 958) = _; rw [producer099]; rfl) (by change host_forest.mask_endpoint_bump (C099 240) = _; rw [consumer099]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link100 : Array.index_usize host_forest.MASK_LINKS 100#usize = ok (251#u16,961#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer100 : P100 251 = 0#u8 := by
  dsimp only [P100, P099, P098, P097, P096, P095, P094, P093, Function.update]
  dsimp only [P092, P091, P090, P089, P088, P087, P086, P085, Function.update]
  dsimp only [P084, P083, P082, P081, P080, P079, P078, P077, Function.update]
  dsimp only [P076, P075, P074, P073, P072, P071, P070, P069, Function.update]
  dsimp only [P068, P067, P066, P065, P064, P063, P062, P061, Function.update]
  dsimp only [P060, P059, P058, P057, P056, P055, P054, P053, Function.update]
  dsimp only [P052, P051, P050, P049, P048, P047, P046, P045, Function.update]
  dsimp only [P044, P043, P042, P041, P040, P039, P038, P037, Function.update]
  dsimp only [P036, P035, P034, P033, P032, P031, P030, P029, Function.update]
  dsimp only [P028, P027, P026, P025, P024, P023, P022, P021, Function.update]
  dsimp only [P020, P019, P018, P017, P016, P015, P014, P013, Function.update]
  dsimp only [P012, P011, P010, P009, P008, P007, P006, P005, Function.update]
  dsimp only [P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer100 : C100 961 = 0#u8 := by
  dsimp only [C100, C099, C098, C097, C096, C095, C094, C093, Function.update]
  dsimp only [C092, C091, C090, C089, C088, C087, C086, C085, Function.update]
  dsimp only [C084, C083, C082, C081, C080, C079, C078, C077, Function.update]
  dsimp only [C076, C075, C074, C073, C072, C071, C070, C069, Function.update]
  dsimp only [C068, C067, C066, C065, C064, C063, C062, C061, Function.update]
  dsimp only [C060, C059, C058, C057, C056, C055, C054, C053, Function.update]
  dsimp only [C052, C051, C050, C049, C048, C047, C046, C045, Function.update]
  dsimp only [C044, C043, C042, C041, C040, C039, C038, C037, Function.update]
  dsimp only [C036, C035, C034, C033, C032, C031, C030, C029, Function.update]
  dsimp only [C028, C027, C026, C025, C024, C023, C022, C021, Function.update]
  dsimp only [C020, C019, C018, C017, C016, C015, C014, C013, Function.update]
  dsimp only [C012, C011, C010, C009, C008, C007, C006, C005, Function.update]
  dsimp only [C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step100 : body s100 = ok (cont s101) := by
  unfold body s100 s101 P101 C101 M101
  have next : Usize.wrapping_add 100#usize 1#usize = 101#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 100#usize (by
      change 101 < Usize.size; simpa using UScalar.hSize (101#usize))
  simpa only [next, show (251#usize).val = 251 from rfl,
    show (961#usize).val = 961 from rfl] using step P100 C100 M100 100#usize 251#usize 961#usize 251#u16 961#u16 1#u8 1#u8
    (by decide) link100 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P100 251) = _; rw [producer100]; rfl) (by change host_forest.mask_endpoint_bump (C100 961) = _; rw [consumer100]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link101 : Array.index_usize host_forest.MASK_LINKS 101#usize = ok (962#u16,268#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer101 : P101 962 = 0#u8 := by
  dsimp only [P101, P100, P099, P098, P097, P096, P095, P094, Function.update]
  dsimp only [P093, P092, P091, P090, P089, P088, P087, P086, Function.update]
  dsimp only [P085, P084, P083, P082, P081, P080, P079, P078, Function.update]
  dsimp only [P077, P076, P075, P074, P073, P072, P071, P070, Function.update]
  dsimp only [P069, P068, P067, P066, P065, P064, P063, P062, Function.update]
  dsimp only [P061, P060, P059, P058, P057, P056, P055, P054, Function.update]
  dsimp only [P053, P052, P051, P050, P049, P048, P047, P046, Function.update]
  dsimp only [P045, P044, P043, P042, P041, P040, P039, P038, Function.update]
  dsimp only [P037, P036, P035, P034, P033, P032, P031, P030, Function.update]
  dsimp only [P029, P028, P027, P026, P025, P024, P023, P022, Function.update]
  dsimp only [P021, P020, P019, P018, P017, P016, P015, P014, Function.update]
  dsimp only [P013, P012, P011, P010, P009, P008, P007, P006, Function.update]
  dsimp only [P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer101 : C101 268 = 0#u8 := by
  dsimp only [C101, C100, C099, C098, C097, C096, C095, C094, Function.update]
  dsimp only [C093, C092, C091, C090, C089, C088, C087, C086, Function.update]
  dsimp only [C085, C084, C083, C082, C081, C080, C079, C078, Function.update]
  dsimp only [C077, C076, C075, C074, C073, C072, C071, C070, Function.update]
  dsimp only [C069, C068, C067, C066, C065, C064, C063, C062, Function.update]
  dsimp only [C061, C060, C059, C058, C057, C056, C055, C054, Function.update]
  dsimp only [C053, C052, C051, C050, C049, C048, C047, C046, Function.update]
  dsimp only [C045, C044, C043, C042, C041, C040, C039, C038, Function.update]
  dsimp only [C037, C036, C035, C034, C033, C032, C031, C030, Function.update]
  dsimp only [C029, C028, C027, C026, C025, C024, C023, C022, Function.update]
  dsimp only [C021, C020, C019, C018, C017, C016, C015, C014, Function.update]
  dsimp only [C013, C012, C011, C010, C009, C008, C007, C006, Function.update]
  dsimp only [C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step101 : body s101 = ok (cont s102) := by
  unfold body s101 s102 P102 C102 M102
  have next : Usize.wrapping_add 101#usize 1#usize = 102#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 101#usize (by
      change 102 < Usize.size; simpa using UScalar.hSize (102#usize))
  simpa only [next, show (962#usize).val = 962 from rfl,
    show (268#usize).val = 268 from rfl] using step P101 C101 M101 101#usize 962#usize 268#usize 962#u16 268#u16 1#u8 1#u8
    (by decide) link101 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P101 962) = _; rw [producer101]; rfl) (by change host_forest.mask_endpoint_bump (C101 268) = _; rw [consumer101]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link102 : Array.index_usize host_forest.MASK_LINKS 102#usize = ok (962#u16,256#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer102 : P102 962 = 1#u8 := by
  dsimp only [P102, P101, P100, P099, P098, P097, P096, P095, Function.update]
  dsimp only [P094, P093, P092, P091, P090, P089, P088, P087, Function.update]
  dsimp only [P086, P085, P084, P083, P082, P081, P080, P079, Function.update]
  dsimp only [P078, P077, P076, P075, P074, P073, P072, P071, Function.update]
  dsimp only [P070, P069, P068, P067, P066, P065, P064, P063, Function.update]
  dsimp only [P062, P061, P060, P059, P058, P057, P056, P055, Function.update]
  dsimp only [P054, P053, P052, P051, P050, P049, P048, P047, Function.update]
  dsimp only [P046, P045, P044, P043, P042, P041, P040, P039, Function.update]
  dsimp only [P038, P037, P036, P035, P034, P033, P032, P031, Function.update]
  dsimp only [P030, P029, P028, P027, P026, P025, P024, P023, Function.update]
  dsimp only [P022, P021, P020, P019, P018, P017, P016, P015, Function.update]
  dsimp only [P014, P013, P012, P011, P010, P009, P008, P007, Function.update]
  dsimp only [P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer102 : C102 256 = 0#u8 := by
  dsimp only [C102, C101, C100, C099, C098, C097, C096, C095, Function.update]
  dsimp only [C094, C093, C092, C091, C090, C089, C088, C087, Function.update]
  dsimp only [C086, C085, C084, C083, C082, C081, C080, C079, Function.update]
  dsimp only [C078, C077, C076, C075, C074, C073, C072, C071, Function.update]
  dsimp only [C070, C069, C068, C067, C066, C065, C064, C063, Function.update]
  dsimp only [C062, C061, C060, C059, C058, C057, C056, C055, Function.update]
  dsimp only [C054, C053, C052, C051, C050, C049, C048, C047, Function.update]
  dsimp only [C046, C045, C044, C043, C042, C041, C040, C039, Function.update]
  dsimp only [C038, C037, C036, C035, C034, C033, C032, C031, Function.update]
  dsimp only [C030, C029, C028, C027, C026, C025, C024, C023, Function.update]
  dsimp only [C022, C021, C020, C019, C018, C017, C016, C015, Function.update]
  dsimp only [C014, C013, C012, C011, C010, C009, C008, C007, Function.update]
  dsimp only [C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step102 : body s102 = ok (cont s103) := by
  unfold body s102 s103 P103 C103 M103
  have next : Usize.wrapping_add 102#usize 1#usize = 103#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 102#usize (by
      change 103 < Usize.size; simpa using UScalar.hSize (103#usize))
  simpa only [next, show (962#usize).val = 962 from rfl,
    show (256#usize).val = 256 from rfl] using step P102 C102 M102 102#usize 962#usize 256#usize 962#u16 256#u16 2#u8 1#u8
    (by decide) link102 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P102 962) = _; rw [producer102]; rfl) (by change host_forest.mask_endpoint_bump (C102 256) = _; rw [consumer102]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link103 : Array.index_usize host_forest.MASK_LINKS 103#usize = ok (267#u16,965#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer103 : P103 267 = 0#u8 := by
  dsimp only [P103, P102, P101, P100, P099, P098, P097, P096, Function.update]
  dsimp only [P095, P094, P093, P092, P091, P090, P089, P088, Function.update]
  dsimp only [P087, P086, P085, P084, P083, P082, P081, P080, Function.update]
  dsimp only [P079, P078, P077, P076, P075, P074, P073, P072, Function.update]
  dsimp only [P071, P070, P069, P068, P067, P066, P065, P064, Function.update]
  dsimp only [P063, P062, P061, P060, P059, P058, P057, P056, Function.update]
  dsimp only [P055, P054, P053, P052, P051, P050, P049, P048, Function.update]
  dsimp only [P047, P046, P045, P044, P043, P042, P041, P040, Function.update]
  dsimp only [P039, P038, P037, P036, P035, P034, P033, P032, Function.update]
  dsimp only [P031, P030, P029, P028, P027, P026, P025, P024, Function.update]
  dsimp only [P023, P022, P021, P020, P019, P018, P017, P016, Function.update]
  dsimp only [P015, P014, P013, P012, P011, P010, P009, P008, Function.update]
  dsimp only [P007, P006, P005, P004, P003, P002, P001, P000, Function.update]
  rfl
theorem consumer103 : C103 965 = 0#u8 := by
  dsimp only [C103, C102, C101, C100, C099, C098, C097, C096, Function.update]
  dsimp only [C095, C094, C093, C092, C091, C090, C089, C088, Function.update]
  dsimp only [C087, C086, C085, C084, C083, C082, C081, C080, Function.update]
  dsimp only [C079, C078, C077, C076, C075, C074, C073, C072, Function.update]
  dsimp only [C071, C070, C069, C068, C067, C066, C065, C064, Function.update]
  dsimp only [C063, C062, C061, C060, C059, C058, C057, C056, Function.update]
  dsimp only [C055, C054, C053, C052, C051, C050, C049, C048, Function.update]
  dsimp only [C047, C046, C045, C044, C043, C042, C041, C040, Function.update]
  dsimp only [C039, C038, C037, C036, C035, C034, C033, C032, Function.update]
  dsimp only [C031, C030, C029, C028, C027, C026, C025, C024, Function.update]
  dsimp only [C023, C022, C021, C020, C019, C018, C017, C016, Function.update]
  dsimp only [C015, C014, C013, C012, C011, C010, C009, C008, Function.update]
  dsimp only [C007, C006, C005, C004, C003, C002, C001, C000, Function.update]
  rfl
theorem step103 : body s103 = ok (cont s104) := by
  unfold body s103 s104 P104 C104 M104
  have next : Usize.wrapping_add 103#usize 1#usize = 104#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 103#usize (by
      change 104 < Usize.size; simpa using UScalar.hSize (104#usize))
  simpa only [next, show (267#usize).val = 267 from rfl,
    show (965#usize).val = 965 from rfl] using step P103 C103 M103 103#usize 267#usize 965#usize 267#u16 965#u16 1#u8 1#u8
    (by decide) link103 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P103 267) = _; rw [producer103]; rfl) (by change host_forest.mask_endpoint_bump (C103 965) = _; rw [consumer103]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s096 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step096).trans ((run_next _ _ step097).trans ((run_next _ _ step098).trans ((run_next _ _ step099).trans ((run_next _ _ step100).trans ((run_next _ _ step101).trans ((run_next _ _ step102).trans ((run_next _ _ step103).trans (PV_B3_MaskSparse13.suffix))))))))
#print axioms link096
#print axioms producer096
#print axioms consumer096
#print axioms step096
#print axioms link097
#print axioms producer097
#print axioms consumer097
#print axioms step097
#print axioms link098
#print axioms producer098
#print axioms consumer098
#print axioms step098
#print axioms link099
#print axioms producer099
#print axioms consumer099
#print axioms step099
#print axioms link100
#print axioms producer100
#print axioms consumer100
#print axioms step100
#print axioms link101
#print axioms producer101
#print axioms consumer101
#print axioms step101
#print axioms link102
#print axioms producer102
#print axioms consumer102
#print axioms step102
#print axioms link103
#print axioms producer103
#print axioms consumer103
#print axioms step103
#print axioms suffix
end PV_B3_MaskSparse12
