import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse14
namespace PV_B3_MaskSparse13
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link104 : Array.index_usize host_forest.MASK_LINKS 104#usize = ok (966#u16,284#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer104 : P104 966 = 0#u8 := by
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
theorem consumer104 : C104 284 = 0#u8 := by
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
theorem step104 : body s104 = ok (cont s105) := by
  unfold body s104 s105 P105 C105 M105
  have next : Usize.wrapping_add 104#usize 1#usize = 105#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 104#usize (by
      change 105 < Usize.size; simpa using UScalar.hSize (105#usize))
  simpa only [next, show (966#usize).val = 966 from rfl,
    show (284#usize).val = 284 from rfl] using step P104 C104 M104 104#usize 966#usize 284#usize 966#u16 284#u16 1#u8 1#u8
    (by decide) link104 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P104 966) = _; rw [producer104]; rfl) (by change host_forest.mask_endpoint_bump (C104 284) = _; rw [consumer104]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link105 : Array.index_usize host_forest.MASK_LINKS 105#usize = ok (966#u16,272#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer105 : P105 966 = 1#u8 := by
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
theorem consumer105 : C105 272 = 0#u8 := by
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
theorem step105 : body s105 = ok (cont s106) := by
  unfold body s105 s106 P106 C106 M106
  have next : Usize.wrapping_add 105#usize 1#usize = 106#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 105#usize (by
      change 106 < Usize.size; simpa using UScalar.hSize (106#usize))
  simpa only [next, show (966#usize).val = 966 from rfl,
    show (272#usize).val = 272 from rfl] using step P105 C105 M105 105#usize 966#usize 272#usize 966#u16 272#u16 2#u8 1#u8
    (by decide) link105 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P105 966) = _; rw [producer105]; rfl) (by change host_forest.mask_endpoint_bump (C105 272) = _; rw [consumer105]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link106 : Array.index_usize host_forest.MASK_LINKS 106#usize = ok (283#u16,969#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer106 : P106 283 = 0#u8 := by
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
theorem consumer106 : C106 969 = 0#u8 := by
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
theorem step106 : body s106 = ok (cont s107) := by
  unfold body s106 s107 P107 C107 M107
  have next : Usize.wrapping_add 106#usize 1#usize = 107#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 106#usize (by
      change 107 < Usize.size; simpa using UScalar.hSize (107#usize))
  simpa only [next, show (283#usize).val = 283 from rfl,
    show (969#usize).val = 969 from rfl] using step P106 C106 M106 106#usize 283#usize 969#usize 283#u16 969#u16 1#u8 1#u8
    (by decide) link106 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P106 283) = _; rw [producer106]; rfl) (by change host_forest.mask_endpoint_bump (C106 969) = _; rw [consumer106]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link107 : Array.index_usize host_forest.MASK_LINKS 107#usize = ok (970#u16,300#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer107 : P107 970 = 0#u8 := by
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
theorem consumer107 : C107 300 = 0#u8 := by
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
theorem step107 : body s107 = ok (cont s108) := by
  unfold body s107 s108 P108 C108 M108
  have next : Usize.wrapping_add 107#usize 1#usize = 108#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 107#usize (by
      change 108 < Usize.size; simpa using UScalar.hSize (108#usize))
  simpa only [next, show (970#usize).val = 970 from rfl,
    show (300#usize).val = 300 from rfl] using step P107 C107 M107 107#usize 970#usize 300#usize 970#u16 300#u16 1#u8 1#u8
    (by decide) link107 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P107 970) = _; rw [producer107]; rfl) (by change host_forest.mask_endpoint_bump (C107 300) = _; rw [consumer107]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link108 : Array.index_usize host_forest.MASK_LINKS 108#usize = ok (970#u16,288#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer108 : P108 970 = 1#u8 := by
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
theorem consumer108 : C108 288 = 0#u8 := by
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
theorem step108 : body s108 = ok (cont s109) := by
  unfold body s108 s109 P109 C109 M109
  have next : Usize.wrapping_add 108#usize 1#usize = 109#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 108#usize (by
      change 109 < Usize.size; simpa using UScalar.hSize (109#usize))
  simpa only [next, show (970#usize).val = 970 from rfl,
    show (288#usize).val = 288 from rfl] using step P108 C108 M108 108#usize 970#usize 288#usize 970#u16 288#u16 2#u8 1#u8
    (by decide) link108 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P108 970) = _; rw [producer108]; rfl) (by change host_forest.mask_endpoint_bump (C108 288) = _; rw [consumer108]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link109 : Array.index_usize host_forest.MASK_LINKS 109#usize = ok (299#u16,973#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer109 : P109 299 = 0#u8 := by
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
theorem consumer109 : C109 973 = 0#u8 := by
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
theorem step109 : body s109 = ok (cont s110) := by
  unfold body s109 s110 P110 C110 M110
  have next : Usize.wrapping_add 109#usize 1#usize = 110#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 109#usize (by
      change 110 < Usize.size; simpa using UScalar.hSize (110#usize))
  simpa only [next, show (299#usize).val = 299 from rfl,
    show (973#usize).val = 973 from rfl] using step P109 C109 M109 109#usize 299#usize 973#usize 299#u16 973#u16 1#u8 1#u8
    (by decide) link109 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P109 299) = _; rw [producer109]; rfl) (by change host_forest.mask_endpoint_bump (C109 973) = _; rw [consumer109]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link110 : Array.index_usize host_forest.MASK_LINKS 110#usize = ok (974#u16,316#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer110 : P110 974 = 0#u8 := by
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
theorem consumer110 : C110 316 = 0#u8 := by
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
theorem step110 : body s110 = ok (cont s111) := by
  unfold body s110 s111 P111 C111 M111
  have next : Usize.wrapping_add 110#usize 1#usize = 111#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 110#usize (by
      change 111 < Usize.size; simpa using UScalar.hSize (111#usize))
  simpa only [next, show (974#usize).val = 974 from rfl,
    show (316#usize).val = 316 from rfl] using step P110 C110 M110 110#usize 974#usize 316#usize 974#u16 316#u16 1#u8 1#u8
    (by decide) link110 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P110 974) = _; rw [producer110]; rfl) (by change host_forest.mask_endpoint_bump (C110 316) = _; rw [consumer110]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link111 : Array.index_usize host_forest.MASK_LINKS 111#usize = ok (974#u16,304#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer111 : P111 974 = 1#u8 := by
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
theorem consumer111 : C111 304 = 0#u8 := by
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
theorem step111 : body s111 = ok (cont s112) := by
  unfold body s111 s112 P112 C112 M112
  have next : Usize.wrapping_add 111#usize 1#usize = 112#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 111#usize (by
      change 112 < Usize.size; simpa using UScalar.hSize (112#usize))
  simpa only [next, show (974#usize).val = 974 from rfl,
    show (304#usize).val = 304 from rfl] using step P111 C111 M111 111#usize 974#usize 304#usize 974#u16 304#u16 2#u8 1#u8
    (by decide) link111 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P111 974) = _; rw [producer111]; rfl) (by change host_forest.mask_endpoint_bump (C111 304) = _; rw [consumer111]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s104 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step104).trans ((run_next _ _ step105).trans ((run_next _ _ step106).trans ((run_next _ _ step107).trans ((run_next _ _ step108).trans ((run_next _ _ step109).trans ((run_next _ _ step110).trans ((run_next _ _ step111).trans (PV_B3_MaskSparse14.suffix))))))))
#print axioms link104
#print axioms producer104
#print axioms consumer104
#print axioms step104
#print axioms link105
#print axioms producer105
#print axioms consumer105
#print axioms step105
#print axioms link106
#print axioms producer106
#print axioms consumer106
#print axioms step106
#print axioms link107
#print axioms producer107
#print axioms consumer107
#print axioms step107
#print axioms link108
#print axioms producer108
#print axioms consumer108
#print axioms step108
#print axioms link109
#print axioms producer109
#print axioms consumer109
#print axioms step109
#print axioms link110
#print axioms producer110
#print axioms consumer110
#print axioms step110
#print axioms link111
#print axioms producer111
#print axioms consumer111
#print axioms step111
#print axioms suffix
end PV_B3_MaskSparse13
