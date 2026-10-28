import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse16
namespace PV_B3_MaskSparse15
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link120 : Array.index_usize host_forest.MASK_LINKS 120#usize = ok (986#u16,352#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer120 : P120 986 = 1#u8 := by
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
theorem consumer120 : C120 352 = 0#u8 := by
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
theorem step120 : body s120 = ok (cont s121) := by
  unfold body s120 s121 P121 C121 M121
  have next : Usize.wrapping_add 120#usize 1#usize = 121#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 120#usize (by
      change 121 < Usize.size; simpa using UScalar.hSize (121#usize))
  simpa only [next, show (986#usize).val = 986 from rfl,
    show (352#usize).val = 352 from rfl] using step P120 C120 M120 120#usize 986#usize 352#usize 986#u16 352#u16 2#u8 1#u8
    (by decide) link120 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P120 986) = _; rw [producer120]; rfl) (by change host_forest.mask_endpoint_bump (C120 352) = _; rw [consumer120]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link121 : Array.index_usize host_forest.MASK_LINKS 121#usize = ok (363#u16,989#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer121 : P121 363 = 0#u8 := by
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
theorem consumer121 : C121 989 = 0#u8 := by
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
theorem step121 : body s121 = ok (cont s122) := by
  unfold body s121 s122 P122 C122 M122
  have next : Usize.wrapping_add 121#usize 1#usize = 122#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 121#usize (by
      change 122 < Usize.size; simpa using UScalar.hSize (122#usize))
  simpa only [next, show (363#usize).val = 363 from rfl,
    show (989#usize).val = 989 from rfl] using step P121 C121 M121 121#usize 363#usize 989#usize 363#u16 989#u16 1#u8 1#u8
    (by decide) link121 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P121 363) = _; rw [producer121]; rfl) (by change host_forest.mask_endpoint_bump (C121 989) = _; rw [consumer121]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link122 : Array.index_usize host_forest.MASK_LINKS 122#usize = ok (990#u16,380#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer122 : P122 990 = 0#u8 := by
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
theorem consumer122 : C122 380 = 0#u8 := by
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
theorem step122 : body s122 = ok (cont s123) := by
  unfold body s122 s123 P123 C123 M123
  have next : Usize.wrapping_add 122#usize 1#usize = 123#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 122#usize (by
      change 123 < Usize.size; simpa using UScalar.hSize (123#usize))
  simpa only [next, show (990#usize).val = 990 from rfl,
    show (380#usize).val = 380 from rfl] using step P122 C122 M122 122#usize 990#usize 380#usize 990#u16 380#u16 1#u8 1#u8
    (by decide) link122 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P122 990) = _; rw [producer122]; rfl) (by change host_forest.mask_endpoint_bump (C122 380) = _; rw [consumer122]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link123 : Array.index_usize host_forest.MASK_LINKS 123#usize = ok (990#u16,368#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer123 : P123 990 = 1#u8 := by
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
theorem consumer123 : C123 368 = 0#u8 := by
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
theorem step123 : body s123 = ok (cont s124) := by
  unfold body s123 s124 P124 C124 M124
  have next : Usize.wrapping_add 123#usize 1#usize = 124#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 123#usize (by
      change 124 < Usize.size; simpa using UScalar.hSize (124#usize))
  simpa only [next, show (990#usize).val = 990 from rfl,
    show (368#usize).val = 368 from rfl] using step P123 C123 M123 123#usize 990#usize 368#usize 990#u16 368#u16 2#u8 1#u8
    (by decide) link123 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P123 990) = _; rw [producer123]; rfl) (by change host_forest.mask_endpoint_bump (C123 368) = _; rw [consumer123]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link124 : Array.index_usize host_forest.MASK_LINKS 124#usize = ok (379#u16,993#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer124 : P124 379 = 0#u8 := by
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
theorem consumer124 : C124 993 = 0#u8 := by
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
theorem step124 : body s124 = ok (cont s125) := by
  unfold body s124 s125 P125 C125 M125
  have next : Usize.wrapping_add 124#usize 1#usize = 125#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 124#usize (by
      change 125 < Usize.size; simpa using UScalar.hSize (125#usize))
  simpa only [next, show (379#usize).val = 379 from rfl,
    show (993#usize).val = 993 from rfl] using step P124 C124 M124 124#usize 379#usize 993#usize 379#u16 993#u16 1#u8 1#u8
    (by decide) link124 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P124 379) = _; rw [producer124]; rfl) (by change host_forest.mask_endpoint_bump (C124 993) = _; rw [consumer124]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link125 : Array.index_usize host_forest.MASK_LINKS 125#usize = ok (994#u16,396#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer125 : P125 994 = 0#u8 := by
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
theorem consumer125 : C125 396 = 0#u8 := by
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
theorem step125 : body s125 = ok (cont s126) := by
  unfold body s125 s126 P126 C126 M126
  have next : Usize.wrapping_add 125#usize 1#usize = 126#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 125#usize (by
      change 126 < Usize.size; simpa using UScalar.hSize (126#usize))
  simpa only [next, show (994#usize).val = 994 from rfl,
    show (396#usize).val = 396 from rfl] using step P125 C125 M125 125#usize 994#usize 396#usize 994#u16 396#u16 1#u8 1#u8
    (by decide) link125 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P125 994) = _; rw [producer125]; rfl) (by change host_forest.mask_endpoint_bump (C125 396) = _; rw [consumer125]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link126 : Array.index_usize host_forest.MASK_LINKS 126#usize = ok (994#u16,384#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer126 : P126 994 = 1#u8 := by
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
theorem consumer126 : C126 384 = 0#u8 := by
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
theorem step126 : body s126 = ok (cont s127) := by
  unfold body s126 s127 P127 C127 M127
  have next : Usize.wrapping_add 126#usize 1#usize = 127#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 126#usize (by
      change 127 < Usize.size; simpa using UScalar.hSize (127#usize))
  simpa only [next, show (994#usize).val = 994 from rfl,
    show (384#usize).val = 384 from rfl] using step P126 C126 M126 126#usize 994#usize 384#usize 994#u16 384#u16 2#u8 1#u8
    (by decide) link126 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P126 994) = _; rw [producer126]; rfl) (by change host_forest.mask_endpoint_bump (C126 384) = _; rw [consumer126]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link127 : Array.index_usize host_forest.MASK_LINKS 127#usize = ok (395#u16,997#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer127 : P127 395 = 0#u8 := by
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
theorem consumer127 : C127 997 = 0#u8 := by
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
theorem step127 : body s127 = ok (cont s128) := by
  unfold body s127 s128 P128 C128 M128
  have next : Usize.wrapping_add 127#usize 1#usize = 128#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 127#usize (by
      change 128 < Usize.size; simpa using UScalar.hSize (128#usize))
  simpa only [next, show (395#usize).val = 395 from rfl,
    show (997#usize).val = 997 from rfl] using step P127 C127 M127 127#usize 395#usize 997#usize 395#u16 997#u16 1#u8 1#u8
    (by decide) link127 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P127 395) = _; rw [producer127]; rfl) (by change host_forest.mask_endpoint_bump (C127 997) = _; rw [consumer127]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s120 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step120).trans ((run_next _ _ step121).trans ((run_next _ _ step122).trans ((run_next _ _ step123).trans ((run_next _ _ step124).trans ((run_next _ _ step125).trans ((run_next _ _ step126).trans ((run_next _ _ step127).trans (PV_B3_MaskSparse16.suffix))))))))
#print axioms link120
#print axioms producer120
#print axioms consumer120
#print axioms step120
#print axioms link121
#print axioms producer121
#print axioms consumer121
#print axioms step121
#print axioms link122
#print axioms producer122
#print axioms consumer122
#print axioms step122
#print axioms link123
#print axioms producer123
#print axioms consumer123
#print axioms step123
#print axioms link124
#print axioms producer124
#print axioms consumer124
#print axioms step124
#print axioms link125
#print axioms producer125
#print axioms consumer125
#print axioms step125
#print axioms link126
#print axioms producer126
#print axioms consumer126
#print axioms step126
#print axioms link127
#print axioms producer127
#print axioms consumer127
#print axioms step127
#print axioms suffix
end PV_B3_MaskSparse15
