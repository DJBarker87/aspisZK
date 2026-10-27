import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
namespace PV_B3_MaskSparse16
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link128 : Array.index_usize host_forest.MASK_LINKS 128#usize = ok (998#u16,876#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer128 : P128 998 = 0#u8 := by
  dsimp only [P128, P127, P126, P125, P124, P123, P122, P121, Function.update]
  dsimp only [P120, P119, P118, P117, P116, P115, P114, P113, Function.update]
  dsimp only [P112, P111, P110, P109, P108, P107, P106, P105, Function.update]
  dsimp only [P104, P103, P102, P101, P100, P099, P098, P097, Function.update]
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
theorem consumer128 : C128 876 = 0#u8 := by
  dsimp only [C128, C127, C126, C125, C124, C123, C122, C121, Function.update]
  dsimp only [C120, C119, C118, C117, C116, C115, C114, C113, Function.update]
  dsimp only [C112, C111, C110, C109, C108, C107, C106, C105, Function.update]
  dsimp only [C104, C103, C102, C101, C100, C099, C098, C097, Function.update]
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
theorem step128 : body s128 = ok (cont s129) := by
  unfold body s128 s129 P129 C129 M129
  have next : Usize.wrapping_add 128#usize 1#usize = 129#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 128#usize (by
      change 129 < Usize.size; simpa using UScalar.hSize (129#usize))
  simpa only [next, show (998#usize).val = 998 from rfl,
    show (876#usize).val = 876 from rfl] using step P128 C128 M128 128#usize 998#usize 876#usize 998#u16 876#u16 1#u8 1#u8
    (by decide) link128 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P128 998) = _; rw [producer128]; rfl) (by change host_forest.mask_endpoint_bump (C128 876) = _; rw [consumer128]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link129 : Array.index_usize host_forest.MASK_LINKS 129#usize = ok (998#u16,864#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer129 : P129 998 = 1#u8 := by
  dsimp only [P129, P128, P127, P126, P125, P124, P123, P122, Function.update]
  dsimp only [P121, P120, P119, P118, P117, P116, P115, P114, Function.update]
  dsimp only [P113, P112, P111, P110, P109, P108, P107, P106, Function.update]
  dsimp only [P105, P104, P103, P102, P101, P100, P099, P098, Function.update]
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
theorem consumer129 : C129 864 = 0#u8 := by
  dsimp only [C129, C128, C127, C126, C125, C124, C123, C122, Function.update]
  dsimp only [C121, C120, C119, C118, C117, C116, C115, C114, Function.update]
  dsimp only [C113, C112, C111, C110, C109, C108, C107, C106, Function.update]
  dsimp only [C105, C104, C103, C102, C101, C100, C099, C098, Function.update]
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
theorem step129 : body s129 = ok (cont s130) := by
  unfold body s129 s130 P130 C130 M130
  have next : Usize.wrapping_add 129#usize 1#usize = 130#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 129#usize (by
      change 130 < Usize.size; simpa using UScalar.hSize (130#usize))
  simpa only [next, show (998#usize).val = 998 from rfl,
    show (864#usize).val = 864 from rfl] using step P129 C129 M129 129#usize 998#usize 864#usize 998#u16 864#u16 2#u8 1#u8
    (by decide) link129 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P129 998) = _; rw [producer129]; rfl) (by change host_forest.mask_endpoint_bump (C129 864) = _; rw [consumer129]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link130 : Array.index_usize host_forest.MASK_LINKS 130#usize = ok (875#u16,1001#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer130 : P130 875 = 0#u8 := by
  dsimp only [P130, P129, P128, P127, P126, P125, P124, P123, Function.update]
  dsimp only [P122, P121, P120, P119, P118, P117, P116, P115, Function.update]
  dsimp only [P114, P113, P112, P111, P110, P109, P108, P107, Function.update]
  dsimp only [P106, P105, P104, P103, P102, P101, P100, P099, Function.update]
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
theorem consumer130 : C130 1001 = 0#u8 := by
  dsimp only [C130, C129, C128, C127, C126, C125, C124, C123, Function.update]
  dsimp only [C122, C121, C120, C119, C118, C117, C116, C115, Function.update]
  dsimp only [C114, C113, C112, C111, C110, C109, C108, C107, Function.update]
  dsimp only [C106, C105, C104, C103, C102, C101, C100, C099, Function.update]
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
theorem step130 : body s130 = ok (cont s131) := by
  unfold body s130 s131 P131 C131 M131
  have next : Usize.wrapping_add 130#usize 1#usize = 131#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 130#usize (by
      change 131 < Usize.size; simpa using UScalar.hSize (131#usize))
  simpa only [next, show (875#usize).val = 875 from rfl,
    show (1001#usize).val = 1001 from rfl] using step P130 C130 M130 130#usize 875#usize 1001#usize 875#u16 1001#u16 1#u8 1#u8
    (by decide) link130 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P130 875) = _; rw [producer130]; rfl) (by change host_forest.mask_endpoint_bump (C130 1001) = _; rw [consumer130]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link131 : Array.index_usize host_forest.MASK_LINKS 131#usize = ok (1002#u16,892#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer131 : P131 1002 = 0#u8 := by
  dsimp only [P131, P130, P129, P128, P127, P126, P125, P124, Function.update]
  dsimp only [P123, P122, P121, P120, P119, P118, P117, P116, Function.update]
  dsimp only [P115, P114, P113, P112, P111, P110, P109, P108, Function.update]
  dsimp only [P107, P106, P105, P104, P103, P102, P101, P100, Function.update]
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
theorem consumer131 : C131 892 = 0#u8 := by
  dsimp only [C131, C130, C129, C128, C127, C126, C125, C124, Function.update]
  dsimp only [C123, C122, C121, C120, C119, C118, C117, C116, Function.update]
  dsimp only [C115, C114, C113, C112, C111, C110, C109, C108, Function.update]
  dsimp only [C107, C106, C105, C104, C103, C102, C101, C100, Function.update]
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
theorem step131 : body s131 = ok (cont s132) := by
  unfold body s131 s132 P132 C132 M132
  have next : Usize.wrapping_add 131#usize 1#usize = 132#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 131#usize (by
      change 132 < Usize.size; simpa using UScalar.hSize (132#usize))
  simpa only [next, show (1002#usize).val = 1002 from rfl,
    show (892#usize).val = 892 from rfl] using step P131 C131 M131 131#usize 1002#usize 892#usize 1002#u16 892#u16 1#u8 1#u8
    (by decide) link131 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P131 1002) = _; rw [producer131]; rfl) (by change host_forest.mask_endpoint_bump (C131 892) = _; rw [consumer131]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link132 : Array.index_usize host_forest.MASK_LINKS 132#usize = ok (1002#u16,880#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer132 : P132 1002 = 1#u8 := by
  dsimp only [P132, P131, P130, P129, P128, P127, P126, P125, Function.update]
  dsimp only [P124, P123, P122, P121, P120, P119, P118, P117, Function.update]
  dsimp only [P116, P115, P114, P113, P112, P111, P110, P109, Function.update]
  dsimp only [P108, P107, P106, P105, P104, P103, P102, P101, Function.update]
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
theorem consumer132 : C132 880 = 0#u8 := by
  dsimp only [C132, C131, C130, C129, C128, C127, C126, C125, Function.update]
  dsimp only [C124, C123, C122, C121, C120, C119, C118, C117, Function.update]
  dsimp only [C116, C115, C114, C113, C112, C111, C110, C109, Function.update]
  dsimp only [C108, C107, C106, C105, C104, C103, C102, C101, Function.update]
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
theorem step132 : body s132 = ok (cont s133) := by
  unfold body s132 s133 P133 C133 M133
  have next : Usize.wrapping_add 132#usize 1#usize = 133#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 132#usize (by
      change 133 < Usize.size; simpa using UScalar.hSize (133#usize))
  simpa only [next, show (1002#usize).val = 1002 from rfl,
    show (880#usize).val = 880 from rfl] using step P132 C132 M132 132#usize 1002#usize 880#usize 1002#u16 880#u16 2#u8 1#u8
    (by decide) link132 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P132 1002) = _; rw [producer132]; rfl) (by change host_forest.mask_endpoint_bump (C132 880) = _; rw [consumer132]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link133 : Array.index_usize host_forest.MASK_LINKS 133#usize = ok (891#u16,1005#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer133 : P133 891 = 0#u8 := by
  dsimp only [P133, P132, P131, P130, P129, P128, P127, P126, Function.update]
  dsimp only [P125, P124, P123, P122, P121, P120, P119, P118, Function.update]
  dsimp only [P117, P116, P115, P114, P113, P112, P111, P110, Function.update]
  dsimp only [P109, P108, P107, P106, P105, P104, P103, P102, Function.update]
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
theorem consumer133 : C133 1005 = 0#u8 := by
  dsimp only [C133, C132, C131, C130, C129, C128, C127, C126, Function.update]
  dsimp only [C125, C124, C123, C122, C121, C120, C119, C118, Function.update]
  dsimp only [C117, C116, C115, C114, C113, C112, C111, C110, Function.update]
  dsimp only [C109, C108, C107, C106, C105, C104, C103, C102, Function.update]
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
theorem step133 : body s133 = ok (cont s134) := by
  unfold body s133 s134 P134 C134 M134
  have next : Usize.wrapping_add 133#usize 1#usize = 134#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 133#usize (by
      change 134 < Usize.size; simpa using UScalar.hSize (134#usize))
  simpa only [next, show (891#usize).val = 891 from rfl,
    show (1005#usize).val = 1005 from rfl] using step P133 C133 M133 133#usize 891#usize 1005#usize 891#u16 1005#u16 1#u8 1#u8
    (by decide) link133 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P133 891) = _; rw [producer133]; rfl) (by change host_forest.mask_endpoint_bump (C133 1005) = _; rw [consumer133]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link134 : Array.index_usize host_forest.MASK_LINKS 134#usize = ok (1006#u16,908#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer134 : P134 1006 = 0#u8 := by
  dsimp only [P134, P133, P132, P131, P130, P129, P128, P127, Function.update]
  dsimp only [P126, P125, P124, P123, P122, P121, P120, P119, Function.update]
  dsimp only [P118, P117, P116, P115, P114, P113, P112, P111, Function.update]
  dsimp only [P110, P109, P108, P107, P106, P105, P104, P103, Function.update]
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
theorem consumer134 : C134 908 = 0#u8 := by
  dsimp only [C134, C133, C132, C131, C130, C129, C128, C127, Function.update]
  dsimp only [C126, C125, C124, C123, C122, C121, C120, C119, Function.update]
  dsimp only [C118, C117, C116, C115, C114, C113, C112, C111, Function.update]
  dsimp only [C110, C109, C108, C107, C106, C105, C104, C103, Function.update]
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
theorem step134 : body s134 = ok (cont s135) := by
  unfold body s134 s135 P135 C135 M135
  have next : Usize.wrapping_add 134#usize 1#usize = 135#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 134#usize (by
      change 135 < Usize.size; simpa using UScalar.hSize (135#usize))
  simpa only [next, show (1006#usize).val = 1006 from rfl,
    show (908#usize).val = 908 from rfl] using step P134 C134 M134 134#usize 1006#usize 908#usize 1006#u16 908#u16 1#u8 1#u8
    (by decide) link134 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P134 1006) = _; rw [producer134]; rfl) (by change host_forest.mask_endpoint_bump (C134 908) = _; rw [consumer134]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link135 : Array.index_usize host_forest.MASK_LINKS 135#usize = ok (1006#u16,896#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer135 : P135 1006 = 1#u8 := by
  dsimp only [P135, P134, P133, P132, P131, P130, P129, P128, Function.update]
  dsimp only [P127, P126, P125, P124, P123, P122, P121, P120, Function.update]
  dsimp only [P119, P118, P117, P116, P115, P114, P113, P112, Function.update]
  dsimp only [P111, P110, P109, P108, P107, P106, P105, P104, Function.update]
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
theorem consumer135 : C135 896 = 0#u8 := by
  dsimp only [C135, C134, C133, C132, C131, C130, C129, C128, Function.update]
  dsimp only [C127, C126, C125, C124, C123, C122, C121, C120, Function.update]
  dsimp only [C119, C118, C117, C116, C115, C114, C113, C112, Function.update]
  dsimp only [C111, C110, C109, C108, C107, C106, C105, C104, Function.update]
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
theorem step135 : body s135 = ok (cont s136) := by
  unfold body s135 s136 P136 C136 M136
  have next : Usize.wrapping_add 135#usize 1#usize = 136#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 135#usize (by
      change 136 < Usize.size; simpa using UScalar.hSize (136#usize))
  simpa only [next, show (1006#usize).val = 1006 from rfl,
    show (896#usize).val = 896 from rfl] using step P135 C135 M135 135#usize 1006#usize 896#usize 1006#u16 896#u16 2#u8 1#u8
    (by decide) link135 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P135 1006) = _; rw [producer135]; rfl) (by change host_forest.mask_endpoint_bump (C135 896) = _; rw [consumer135]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem finish : run s136 = ok (.Ok (array 64#usize M136)) := by
  unfold run
  rw [loop.eq_def]
  change (do let cf ← body s136; match cf with
    | .cont t => loop body t
    | .done value => ok value) = _
  have hd : body s136 = ok (done (.Ok (array 64#usize M136))) := by
    unfold body s136 host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
    rw [if_neg (by decide)]
  rw [hd]
  rfl
theorem suffix : run s128 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step128).trans ((run_next _ _ step129).trans ((run_next _ _ step130).trans ((run_next _ _ step131).trans ((run_next _ _ step132).trans ((run_next _ _ step133).trans ((run_next _ _ step134).trans ((run_next _ _ step135).trans (finish))))))))
#print axioms link128
#print axioms producer128
#print axioms consumer128
#print axioms step128
#print axioms link129
#print axioms producer129
#print axioms consumer129
#print axioms step129
#print axioms link130
#print axioms producer130
#print axioms consumer130
#print axioms step130
#print axioms link131
#print axioms producer131
#print axioms consumer131
#print axioms step131
#print axioms link132
#print axioms producer132
#print axioms consumer132
#print axioms step132
#print axioms link133
#print axioms producer133
#print axioms consumer133
#print axioms step133
#print axioms link134
#print axioms producer134
#print axioms consumer134
#print axioms step134
#print axioms link135
#print axioms producer135
#print axioms consumer135
#print axioms step135
#print axioms finish
#print axioms suffix
end PV_B3_MaskSparse16
