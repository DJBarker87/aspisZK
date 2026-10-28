import PV_B3_MaskSparseStates
namespace PV_B3_MaskSparse67
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
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
  exact step P134 C134 M134 134#usize 1006#usize 908#usize 1006#u16 908#u16 1#u8 1#u8
    (by decide) link134 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P134 1006) = _; rw [producer134]; rfl) (by change host_forest.mask_endpoint_bump (C134 908) = _; rw [consumer134]; rfl) (by decide) (by decide)
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
  exact step P135 C135 M135 135#usize 1006#usize 896#usize 1006#u16 896#u16 2#u8 1#u8
    (by decide) link135 (by scalar_tac) (by scalar_tac) (by decide) (by decide)
    (by change host_forest.mask_endpoint_bump (P135 1006) = _; rw [producer135]; rfl) (by change host_forest.mask_endpoint_bump (C135 896) = _; rw [consumer135]; rfl) (by decide) (by decide)
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
theorem suffix : run s134 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step134).trans ((run_next _ _ step135).trans finish)
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
end PV_B3_MaskSparse67
