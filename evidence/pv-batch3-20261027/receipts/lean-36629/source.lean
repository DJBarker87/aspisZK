import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse15
namespace PV_B3_MaskSparse14
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link112 : Array.index_usize host_forest.MASK_LINKS 112#usize = ok (315#u16,977#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer112 : P112 315 = 0#u8 := by
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
theorem consumer112 : C112 977 = 0#u8 := by
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
theorem step112 : body s112 = ok (cont s113) := by
  unfold body s112 s113 P113 C113 M113
  have next : Usize.wrapping_add 112#usize 1#usize = 113#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 112#usize (by
      change 113 < Usize.size; simpa using UScalar.hSize (113#usize))
  simpa only [next, show (315#usize).val = 315 from rfl,
    show (977#usize).val = 977 from rfl] using step P112 C112 M112 112#usize 315#usize 977#usize 315#u16 977#u16 1#u8 1#u8
    (by decide) link112 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P112 315) = _; rw [producer112]; rfl) (by change host_forest.mask_endpoint_bump (C112 977) = _; rw [consumer112]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link113 : Array.index_usize host_forest.MASK_LINKS 113#usize = ok (978#u16,332#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer113 : P113 978 = 0#u8 := by
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
theorem consumer113 : C113 332 = 0#u8 := by
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
theorem step113 : body s113 = ok (cont s114) := by
  unfold body s113 s114 P114 C114 M114
  have next : Usize.wrapping_add 113#usize 1#usize = 114#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 113#usize (by
      change 114 < Usize.size; simpa using UScalar.hSize (114#usize))
  simpa only [next, show (978#usize).val = 978 from rfl,
    show (332#usize).val = 332 from rfl] using step P113 C113 M113 113#usize 978#usize 332#usize 978#u16 332#u16 1#u8 1#u8
    (by decide) link113 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P113 978) = _; rw [producer113]; rfl) (by change host_forest.mask_endpoint_bump (C113 332) = _; rw [consumer113]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link114 : Array.index_usize host_forest.MASK_LINKS 114#usize = ok (978#u16,320#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer114 : P114 978 = 1#u8 := by
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
theorem consumer114 : C114 320 = 0#u8 := by
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
theorem step114 : body s114 = ok (cont s115) := by
  unfold body s114 s115 P115 C115 M115
  have next : Usize.wrapping_add 114#usize 1#usize = 115#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 114#usize (by
      change 115 < Usize.size; simpa using UScalar.hSize (115#usize))
  simpa only [next, show (978#usize).val = 978 from rfl,
    show (320#usize).val = 320 from rfl] using step P114 C114 M114 114#usize 978#usize 320#usize 978#u16 320#u16 2#u8 1#u8
    (by decide) link114 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P114 978) = _; rw [producer114]; rfl) (by change host_forest.mask_endpoint_bump (C114 320) = _; rw [consumer114]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link115 : Array.index_usize host_forest.MASK_LINKS 115#usize = ok (331#u16,981#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer115 : P115 331 = 0#u8 := by
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
theorem consumer115 : C115 981 = 0#u8 := by
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
theorem step115 : body s115 = ok (cont s116) := by
  unfold body s115 s116 P116 C116 M116
  have next : Usize.wrapping_add 115#usize 1#usize = 116#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 115#usize (by
      change 116 < Usize.size; simpa using UScalar.hSize (116#usize))
  simpa only [next, show (331#usize).val = 331 from rfl,
    show (981#usize).val = 981 from rfl] using step P115 C115 M115 115#usize 331#usize 981#usize 331#u16 981#u16 1#u8 1#u8
    (by decide) link115 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P115 331) = _; rw [producer115]; rfl) (by change host_forest.mask_endpoint_bump (C115 981) = _; rw [consumer115]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link116 : Array.index_usize host_forest.MASK_LINKS 116#usize = ok (982#u16,348#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer116 : P116 982 = 0#u8 := by
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
theorem consumer116 : C116 348 = 0#u8 := by
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
theorem step116 : body s116 = ok (cont s117) := by
  unfold body s116 s117 P117 C117 M117
  have next : Usize.wrapping_add 116#usize 1#usize = 117#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 116#usize (by
      change 117 < Usize.size; simpa using UScalar.hSize (117#usize))
  simpa only [next, show (982#usize).val = 982 from rfl,
    show (348#usize).val = 348 from rfl] using step P116 C116 M116 116#usize 982#usize 348#usize 982#u16 348#u16 1#u8 1#u8
    (by decide) link116 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P116 982) = _; rw [producer116]; rfl) (by change host_forest.mask_endpoint_bump (C116 348) = _; rw [consumer116]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link117 : Array.index_usize host_forest.MASK_LINKS 117#usize = ok (982#u16,336#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer117 : P117 982 = 1#u8 := by
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
theorem consumer117 : C117 336 = 0#u8 := by
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
theorem step117 : body s117 = ok (cont s118) := by
  unfold body s117 s118 P118 C118 M118
  have next : Usize.wrapping_add 117#usize 1#usize = 118#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 117#usize (by
      change 118 < Usize.size; simpa using UScalar.hSize (118#usize))
  simpa only [next, show (982#usize).val = 982 from rfl,
    show (336#usize).val = 336 from rfl] using step P117 C117 M117 117#usize 982#usize 336#usize 982#u16 336#u16 2#u8 1#u8
    (by decide) link117 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P117 982) = _; rw [producer117]; rfl) (by change host_forest.mask_endpoint_bump (C117 336) = _; rw [consumer117]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link118 : Array.index_usize host_forest.MASK_LINKS 118#usize = ok (347#u16,985#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer118 : P118 347 = 0#u8 := by
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
theorem consumer118 : C118 985 = 0#u8 := by
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
theorem step118 : body s118 = ok (cont s119) := by
  unfold body s118 s119 P119 C119 M119
  have next : Usize.wrapping_add 118#usize 1#usize = 119#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 118#usize (by
      change 119 < Usize.size; simpa using UScalar.hSize (119#usize))
  simpa only [next, show (347#usize).val = 347 from rfl,
    show (985#usize).val = 985 from rfl] using step P118 C118 M118 118#usize 347#usize 985#usize 347#u16 985#u16 1#u8 1#u8
    (by decide) link118 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P118 347) = _; rw [producer118]; rfl) (by change host_forest.mask_endpoint_bump (C118 985) = _; rw [consumer118]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link119 : Array.index_usize host_forest.MASK_LINKS 119#usize = ok (986#u16,364#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer119 : P119 986 = 0#u8 := by
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
theorem consumer119 : C119 364 = 0#u8 := by
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
theorem step119 : body s119 = ok (cont s120) := by
  unfold body s119 s120 P120 C120 M120
  have next : Usize.wrapping_add 119#usize 1#usize = 120#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 119#usize (by
      change 120 < Usize.size; simpa using UScalar.hSize (120#usize))
  simpa only [next, show (986#usize).val = 986 from rfl,
    show (364#usize).val = 364 from rfl] using step P119 C119 M119 119#usize 986#usize 364#usize 986#u16 364#u16 1#u8 1#u8
    (by decide) link119 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P119 986) = _; rw [producer119]; rfl) (by change host_forest.mask_endpoint_bump (C119 364) = _; rw [consumer119]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s112 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step112).trans ((run_next _ _ step113).trans ((run_next _ _ step114).trans ((run_next _ _ step115).trans ((run_next _ _ step116).trans ((run_next _ _ step117).trans ((run_next _ _ step118).trans ((run_next _ _ step119).trans (PV_B3_MaskSparse15.suffix))))))))
#print axioms link112
#print axioms producer112
#print axioms consumer112
#print axioms step112
#print axioms link113
#print axioms producer113
#print axioms consumer113
#print axioms step113
#print axioms link114
#print axioms producer114
#print axioms consumer114
#print axioms step114
#print axioms link115
#print axioms producer115
#print axioms consumer115
#print axioms step115
#print axioms link116
#print axioms producer116
#print axioms consumer116
#print axioms step116
#print axioms link117
#print axioms producer117
#print axioms consumer117
#print axioms step117
#print axioms link118
#print axioms producer118
#print axioms consumer118
#print axioms step118
#print axioms link119
#print axioms producer119
#print axioms consumer119
#print axioms step119
#print axioms suffix
end PV_B3_MaskSparse14
