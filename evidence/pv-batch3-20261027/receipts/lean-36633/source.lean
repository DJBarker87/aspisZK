import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse12
namespace PV_B3_MaskSparse11
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link088 : Array.index_usize host_forest.MASK_LINKS 88#usize = ok (187#u16,945#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer088 : P088 187 = 0#u8 := by
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
theorem consumer088 : C088 945 = 0#u8 := by
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
theorem step088 : body s088 = ok (cont s089) := by
  unfold body s088 s089 P089 C089 M089
  have next : Usize.wrapping_add 88#usize 1#usize = 89#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 88#usize (by
      change 89 < Usize.size; simpa using UScalar.hSize (89#usize))
  simpa only [next, show (187#usize).val = 187 from rfl,
    show (945#usize).val = 945 from rfl] using step P088 C088 M088 88#usize 187#usize 945#usize 187#u16 945#u16 1#u8 1#u8
    (by decide) link088 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P088 187) = _; rw [producer088]; rfl) (by change host_forest.mask_endpoint_bump (C088 945) = _; rw [consumer088]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link089 : Array.index_usize host_forest.MASK_LINKS 89#usize = ok (946#u16,204#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer089 : P089 946 = 0#u8 := by
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
theorem consumer089 : C089 204 = 0#u8 := by
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
theorem step089 : body s089 = ok (cont s090) := by
  unfold body s089 s090 P090 C090 M090
  have next : Usize.wrapping_add 89#usize 1#usize = 90#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 89#usize (by
      change 90 < Usize.size; simpa using UScalar.hSize (90#usize))
  simpa only [next, show (946#usize).val = 946 from rfl,
    show (204#usize).val = 204 from rfl] using step P089 C089 M089 89#usize 946#usize 204#usize 946#u16 204#u16 1#u8 1#u8
    (by decide) link089 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P089 946) = _; rw [producer089]; rfl) (by change host_forest.mask_endpoint_bump (C089 204) = _; rw [consumer089]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link090 : Array.index_usize host_forest.MASK_LINKS 90#usize = ok (946#u16,192#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer090 : P090 946 = 1#u8 := by
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
theorem consumer090 : C090 192 = 0#u8 := by
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
theorem step090 : body s090 = ok (cont s091) := by
  unfold body s090 s091 P091 C091 M091
  have next : Usize.wrapping_add 90#usize 1#usize = 91#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 90#usize (by
      change 91 < Usize.size; simpa using UScalar.hSize (91#usize))
  simpa only [next, show (946#usize).val = 946 from rfl,
    show (192#usize).val = 192 from rfl] using step P090 C090 M090 90#usize 946#usize 192#usize 946#u16 192#u16 2#u8 1#u8
    (by decide) link090 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P090 946) = _; rw [producer090]; rfl) (by change host_forest.mask_endpoint_bump (C090 192) = _; rw [consumer090]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link091 : Array.index_usize host_forest.MASK_LINKS 91#usize = ok (203#u16,949#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer091 : P091 203 = 0#u8 := by
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
theorem consumer091 : C091 949 = 0#u8 := by
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
theorem step091 : body s091 = ok (cont s092) := by
  unfold body s091 s092 P092 C092 M092
  have next : Usize.wrapping_add 91#usize 1#usize = 92#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 91#usize (by
      change 92 < Usize.size; simpa using UScalar.hSize (92#usize))
  simpa only [next, show (203#usize).val = 203 from rfl,
    show (949#usize).val = 949 from rfl] using step P091 C091 M091 91#usize 203#usize 949#usize 203#u16 949#u16 1#u8 1#u8
    (by decide) link091 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P091 203) = _; rw [producer091]; rfl) (by change host_forest.mask_endpoint_bump (C091 949) = _; rw [consumer091]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link092 : Array.index_usize host_forest.MASK_LINKS 92#usize = ok (950#u16,220#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer092 : P092 950 = 0#u8 := by
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
theorem consumer092 : C092 220 = 0#u8 := by
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
theorem step092 : body s092 = ok (cont s093) := by
  unfold body s092 s093 P093 C093 M093
  have next : Usize.wrapping_add 92#usize 1#usize = 93#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 92#usize (by
      change 93 < Usize.size; simpa using UScalar.hSize (93#usize))
  simpa only [next, show (950#usize).val = 950 from rfl,
    show (220#usize).val = 220 from rfl] using step P092 C092 M092 92#usize 950#usize 220#usize 950#u16 220#u16 1#u8 1#u8
    (by decide) link092 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P092 950) = _; rw [producer092]; rfl) (by change host_forest.mask_endpoint_bump (C092 220) = _; rw [consumer092]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link093 : Array.index_usize host_forest.MASK_LINKS 93#usize = ok (950#u16,208#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer093 : P093 950 = 1#u8 := by
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
theorem consumer093 : C093 208 = 0#u8 := by
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
theorem step093 : body s093 = ok (cont s094) := by
  unfold body s093 s094 P094 C094 M094
  have next : Usize.wrapping_add 93#usize 1#usize = 94#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 93#usize (by
      change 94 < Usize.size; simpa using UScalar.hSize (94#usize))
  simpa only [next, show (950#usize).val = 950 from rfl,
    show (208#usize).val = 208 from rfl] using step P093 C093 M093 93#usize 950#usize 208#usize 950#u16 208#u16 2#u8 1#u8
    (by decide) link093 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P093 950) = _; rw [producer093]; rfl) (by change host_forest.mask_endpoint_bump (C093 208) = _; rw [consumer093]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link094 : Array.index_usize host_forest.MASK_LINKS 94#usize = ok (219#u16,953#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer094 : P094 219 = 0#u8 := by
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
theorem consumer094 : C094 953 = 0#u8 := by
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
theorem step094 : body s094 = ok (cont s095) := by
  unfold body s094 s095 P095 C095 M095
  have next : Usize.wrapping_add 94#usize 1#usize = 95#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 94#usize (by
      change 95 < Usize.size; simpa using UScalar.hSize (95#usize))
  simpa only [next, show (219#usize).val = 219 from rfl,
    show (953#usize).val = 953 from rfl] using step P094 C094 M094 94#usize 219#usize 953#usize 219#u16 953#u16 1#u8 1#u8
    (by decide) link094 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P094 219) = _; rw [producer094]; rfl) (by change host_forest.mask_endpoint_bump (C094 953) = _; rw [consumer094]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link095 : Array.index_usize host_forest.MASK_LINKS 95#usize = ok (954#u16,236#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer095 : P095 954 = 0#u8 := by
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
theorem consumer095 : C095 236 = 0#u8 := by
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
theorem step095 : body s095 = ok (cont s096) := by
  unfold body s095 s096 P096 C096 M096
  have next : Usize.wrapping_add 95#usize 1#usize = 96#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 95#usize (by
      change 96 < Usize.size; simpa using UScalar.hSize (96#usize))
  simpa only [next, show (954#usize).val = 954 from rfl,
    show (236#usize).val = 236 from rfl] using step P095 C095 M095 95#usize 954#usize 236#usize 954#u16 236#u16 1#u8 1#u8
    (by decide) link095 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P095 954) = _; rw [producer095]; rfl) (by change host_forest.mask_endpoint_bump (C095 236) = _; rw [consumer095]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s088 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step088).trans ((run_next _ _ step089).trans ((run_next _ _ step090).trans ((run_next _ _ step091).trans ((run_next _ _ step092).trans ((run_next _ _ step093).trans ((run_next _ _ step094).trans ((run_next _ _ step095).trans (PV_B3_MaskSparse12.suffix))))))))
#print axioms link088
#print axioms producer088
#print axioms consumer088
#print axioms step088
#print axioms link089
#print axioms producer089
#print axioms consumer089
#print axioms step089
#print axioms link090
#print axioms producer090
#print axioms consumer090
#print axioms step090
#print axioms link091
#print axioms producer091
#print axioms consumer091
#print axioms step091
#print axioms link092
#print axioms producer092
#print axioms consumer092
#print axioms step092
#print axioms link093
#print axioms producer093
#print axioms consumer093
#print axioms step093
#print axioms link094
#print axioms producer094
#print axioms consumer094
#print axioms step094
#print axioms link095
#print axioms producer095
#print axioms consumer095
#print axioms step095
#print axioms suffix
end PV_B3_MaskSparse11
