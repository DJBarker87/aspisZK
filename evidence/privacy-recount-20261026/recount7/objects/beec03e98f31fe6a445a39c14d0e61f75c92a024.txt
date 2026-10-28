import PV_B3_MaskSparseStates
import PV_B3_MaskSparseScalar
import PV_B3_MaskSparse11
namespace PV_B3_MaskSparse10
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link080 : Array.index_usize host_forest.MASK_LINKS 80#usize = ok (934#u16,156#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer080 : P080 934 = 0#u8 := by
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
theorem consumer080 : C080 156 = 0#u8 := by
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
theorem step080 : body s080 = ok (cont s081) := by
  unfold body s080 s081 P081 C081 M081
  have next : Usize.wrapping_add 80#usize 1#usize = 81#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 80#usize (by
      change 81 < Usize.size; simpa using UScalar.hSize (81#usize))
  simpa only [next, show (934#usize).val = 934 from rfl,
    show (156#usize).val = 156 from rfl] using step P080 C080 M080 80#usize 934#usize 156#usize 934#u16 156#u16 1#u8 1#u8
    (by decide) link080 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P080 934) = _; rw [producer080]; rfl) (by change host_forest.mask_endpoint_bump (C080 156) = _; rw [consumer080]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link081 : Array.index_usize host_forest.MASK_LINKS 81#usize = ok (934#u16,144#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer081 : P081 934 = 1#u8 := by
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
theorem consumer081 : C081 144 = 0#u8 := by
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
theorem step081 : body s081 = ok (cont s082) := by
  unfold body s081 s082 P082 C082 M082
  have next : Usize.wrapping_add 81#usize 1#usize = 82#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 81#usize (by
      change 82 < Usize.size; simpa using UScalar.hSize (82#usize))
  simpa only [next, show (934#usize).val = 934 from rfl,
    show (144#usize).val = 144 from rfl] using step P081 C081 M081 81#usize 934#usize 144#usize 934#u16 144#u16 2#u8 1#u8
    (by decide) link081 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P081 934) = _; rw [producer081]; rfl) (by change host_forest.mask_endpoint_bump (C081 144) = _; rw [consumer081]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link082 : Array.index_usize host_forest.MASK_LINKS 82#usize = ok (155#u16,937#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer082 : P082 155 = 0#u8 := by
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
theorem consumer082 : C082 937 = 0#u8 := by
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
theorem step082 : body s082 = ok (cont s083) := by
  unfold body s082 s083 P083 C083 M083
  have next : Usize.wrapping_add 82#usize 1#usize = 83#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 82#usize (by
      change 83 < Usize.size; simpa using UScalar.hSize (83#usize))
  simpa only [next, show (155#usize).val = 155 from rfl,
    show (937#usize).val = 937 from rfl] using step P082 C082 M082 82#usize 155#usize 937#usize 155#u16 937#u16 1#u8 1#u8
    (by decide) link082 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P082 155) = _; rw [producer082]; rfl) (by change host_forest.mask_endpoint_bump (C082 937) = _; rw [consumer082]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link083 : Array.index_usize host_forest.MASK_LINKS 83#usize = ok (938#u16,172#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer083 : P083 938 = 0#u8 := by
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
theorem consumer083 : C083 172 = 0#u8 := by
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
theorem step083 : body s083 = ok (cont s084) := by
  unfold body s083 s084 P084 C084 M084
  have next : Usize.wrapping_add 83#usize 1#usize = 84#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 83#usize (by
      change 84 < Usize.size; simpa using UScalar.hSize (84#usize))
  simpa only [next, show (938#usize).val = 938 from rfl,
    show (172#usize).val = 172 from rfl] using step P083 C083 M083 83#usize 938#usize 172#usize 938#u16 172#u16 1#u8 1#u8
    (by decide) link083 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P083 938) = _; rw [producer083]; rfl) (by change host_forest.mask_endpoint_bump (C083 172) = _; rw [consumer083]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link084 : Array.index_usize host_forest.MASK_LINKS 84#usize = ok (938#u16,160#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer084 : P084 938 = 1#u8 := by
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
theorem consumer084 : C084 160 = 0#u8 := by
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
theorem step084 : body s084 = ok (cont s085) := by
  unfold body s084 s085 P085 C085 M085
  have next : Usize.wrapping_add 84#usize 1#usize = 85#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 84#usize (by
      change 85 < Usize.size; simpa using UScalar.hSize (85#usize))
  simpa only [next, show (938#usize).val = 938 from rfl,
    show (160#usize).val = 160 from rfl] using step P084 C084 M084 84#usize 938#usize 160#usize 938#u16 160#u16 2#u8 1#u8
    (by decide) link084 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P084 938) = _; rw [producer084]; rfl) (by change host_forest.mask_endpoint_bump (C084 160) = _; rw [consumer084]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link085 : Array.index_usize host_forest.MASK_LINKS 85#usize = ok (171#u16,941#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer085 : P085 171 = 0#u8 := by
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
theorem consumer085 : C085 941 = 0#u8 := by
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
theorem step085 : body s085 = ok (cont s086) := by
  unfold body s085 s086 P086 C086 M086
  have next : Usize.wrapping_add 85#usize 1#usize = 86#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 85#usize (by
      change 86 < Usize.size; simpa using UScalar.hSize (86#usize))
  simpa only [next, show (171#usize).val = 171 from rfl,
    show (941#usize).val = 941 from rfl] using step P085 C085 M085 85#usize 171#usize 941#usize 171#u16 941#u16 1#u8 1#u8
    (by decide) link085 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P085 171) = _; rw [producer085]; rfl) (by change host_forest.mask_endpoint_bump (C085 941) = _; rw [consumer085]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link086 : Array.index_usize host_forest.MASK_LINKS 86#usize = ok (942#u16,188#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer086 : P086 942 = 0#u8 := by
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
theorem consumer086 : C086 188 = 0#u8 := by
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
theorem step086 : body s086 = ok (cont s087) := by
  unfold body s086 s087 P087 C087 M087
  have next : Usize.wrapping_add 86#usize 1#usize = 87#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 86#usize (by
      change 87 < Usize.size; simpa using UScalar.hSize (87#usize))
  simpa only [next, show (942#usize).val = 942 from rfl,
    show (188#usize).val = 188 from rfl] using step P086 C086 M086 86#usize 942#usize 188#usize 942#u16 188#u16 1#u8 1#u8
    (by decide) link086 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P086 942) = _; rw [producer086]; rfl) (by change host_forest.mask_endpoint_bump (C086 188) = _; rw [consumer086]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem link087 : Array.index_usize host_forest.MASK_LINKS 87#usize = ok (942#u16,176#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer087 : P087 942 = 1#u8 := by
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
theorem consumer087 : C087 176 = 0#u8 := by
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
theorem step087 : body s087 = ok (cont s088) := by
  unfold body s087 s088 P088 C088 M088
  have next : Usize.wrapping_add 87#usize 1#usize = 88#usize := by
    apply UScalar.eq_of_val_eq
    exact PV_B3_MaskSparseScalar.next_value 87#usize (by
      change 88 < Usize.size; simpa using UScalar.hSize (88#usize))
  simpa only [next, show (942#usize).val = 942 from rfl,
    show (176#usize).val = 176 from rfl] using step P087 C087 M087 87#usize 942#usize 176#usize 942#u16 176#u16 2#u8 1#u8
    (by decide) link087 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P087 942) = _; rw [producer087]; rfl) (by change host_forest.mask_endpoint_bump (C087 176) = _; rw [consumer087]; rfl) (by rw [PV_B3_MaskSparseScalar.block_value]; decide) (by rw [PV_B3_MaskSparseScalar.block_value]; decide)
theorem suffix : run s080 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step080).trans ((run_next _ _ step081).trans ((run_next _ _ step082).trans ((run_next _ _ step083).trans ((run_next _ _ step084).trans ((run_next _ _ step085).trans ((run_next _ _ step086).trans ((run_next _ _ step087).trans (PV_B3_MaskSparse11.suffix))))))))
#print axioms link080
#print axioms producer080
#print axioms consumer080
#print axioms step080
#print axioms link081
#print axioms producer081
#print axioms consumer081
#print axioms step081
#print axioms link082
#print axioms producer082
#print axioms consumer082
#print axioms step082
#print axioms link083
#print axioms producer083
#print axioms consumer083
#print axioms step083
#print axioms link084
#print axioms producer084
#print axioms consumer084
#print axioms step084
#print axioms link085
#print axioms producer085
#print axioms consumer085
#print axioms step085
#print axioms link086
#print axioms producer086
#print axioms consumer086
#print axioms step086
#print axioms link087
#print axioms producer087
#print axioms consumer087
#print axioms step087
#print axioms suffix
end PV_B3_MaskSparse10
