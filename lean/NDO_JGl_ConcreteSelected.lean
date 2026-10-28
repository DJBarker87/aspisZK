import NDO_JGl_SelectedCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_ConcreteSelected
open Aeneas Aeneas.Std Result FIq_Native
open JGl_SelectedCells
open FIw_ArrayValue (cells)
def data : Selected := ⟨
  [FIq_Carriers.toQ JFu_ClaimsData.q000,FIq_Carriers.toQ JFu_ClaimsData.q001,FIq_Carriers.toQ JFu_ClaimsData.q002,FIq_Carriers.toQ JFu_ClaimsData.q003,FIq_Carriers.toQ JFu_ClaimsData.q004,FIq_Carriers.toQ JFu_ClaimsData.q005,FIq_Carriers.toQ JFu_ClaimsData.q006,FIq_Carriers.toQ JFu_ClaimsData.q007,FIq_Carriers.toQ JFu_ClaimsData.q008,FIq_Carriers.toQ JFu_ClaimsData.q009,FIq_Carriers.toQ JFu_ClaimsData.q010,FIq_Carriers.toQ JFu_ClaimsData.q011,FIq_Carriers.toQ JFu_ClaimsData.q012,FIq_Carriers.toQ JFu_ClaimsData.q013,FIq_Carriers.toQ JFu_ClaimsData.q014,FIq_Carriers.toQ JFu_ClaimsData.q015,FIq_Carriers.toQ JFu_ClaimsData.q016,FIq_Carriers.toQ JFu_ClaimsData.q017,FIq_Carriers.toQ JFu_ClaimsData.q018,FIq_Carriers.toQ JFu_ClaimsData.q019,FIq_Carriers.toQ JFu_ClaimsData.q020,FIq_Carriers.toQ JFu_ClaimsData.q021,FIq_Carriers.toQ JFu_ClaimsData.q022,FIq_Carriers.toQ JFu_ClaimsData.q023,FIq_Carriers.toQ JFu_ClaimsData.q024,FIq_Carriers.toQ JFu_ClaimsData.q025,FIq_Carriers.toQ JFu_ClaimsData.q026,FIq_Carriers.toQ JFu_ClaimsData.q027,FIq_Carriers.toQ JFu_ClaimsData.q029,FIq_Carriers.toQ JFu_ClaimsData.q030,FIq_Carriers.toQ JFu_ClaimsData.q031,FIq_Carriers.toQ JFu_ClaimsData.q032,FIq_Carriers.toQ JFu_ClaimsData.q033,FIq_Carriers.toQ JFu_ClaimsData.q034,FIq_Carriers.toQ JFu_ClaimsData.q035,FIq_Carriers.toQ JFu_ClaimsData.q036,FIq_Carriers.toQ JFu_ClaimsData.q037,FIq_Carriers.toQ JFu_ClaimsData.q038,FIq_Carriers.toQ JFu_ClaimsData.q039,FIq_Carriers.toQ JFu_ClaimsData.q040,FIq_Carriers.toQ JFu_ClaimsData.q041,FIq_Carriers.toQ JFu_ClaimsData.q042,FIq_Carriers.toQ JFu_ClaimsData.q043,FIq_Carriers.toQ JFu_ClaimsData.q044,FIq_Carriers.toQ JFu_ClaimsData.q045,FIq_Carriers.toQ JFu_ClaimsData.q046,FIq_Carriers.toQ JFu_ClaimsData.q047,FIq_Carriers.toQ JFu_ClaimsData.q048,FIq_Carriers.toQ JFu_ClaimsData.q049,FIq_Carriers.toQ JFu_ClaimsData.q050,FIq_Carriers.toQ JFu_ClaimsData.q051,FIq_Carriers.toQ JFu_ClaimsData.q052,FIq_Carriers.toQ JFu_ClaimsData.q053,FIq_Carriers.toQ JFu_ClaimsData.q054,FIq_Carriers.toQ JFu_ClaimsData.q055,FIq_Carriers.toQ JFu_ClaimsData.q056,FIq_Carriers.toQ JFu_ClaimsData.q058,FIq_Carriers.toQ JFu_ClaimsData.q059,FIq_Carriers.toQ JFu_ClaimsData.q060,FIq_Carriers.toQ JFu_ClaimsData.q061,FIq_Carriers.toQ JFu_ClaimsData.q062,FIq_Carriers.toQ JFu_ClaimsData.q063,FIq_Carriers.toQ JFu_ClaimsData.q064,FIq_Carriers.toQ JFu_ClaimsData.q065,FIq_Carriers.toQ JFu_ClaimsData.q066,FIq_Carriers.toQ JFu_ClaimsData.q067,FIq_Carriers.toQ JFu_ClaimsData.q068,FIq_Carriers.toQ JFu_ClaimsData.q069,FIq_Carriers.toQ JFu_ClaimsData.q070,FIq_Carriers.toQ JFu_ClaimsData.q071,FIq_Carriers.toQ JFu_ClaimsData.q072,FIq_Carriers.toQ JFu_ClaimsData.q073,FIq_Carriers.toQ JFu_ClaimsData.q074,FIq_Carriers.toQ JFu_ClaimsData.q075,FIq_Carriers.toQ JFu_ClaimsData.q076,FIq_Carriers.toQ JFu_ClaimsData.q077,FIq_Carriers.toQ JFu_ClaimsData.q078,FIq_Carriers.toQ JFu_ClaimsData.q079,FIq_Carriers.toQ JFu_ClaimsData.q080,FIq_Carriers.toQ JFu_ClaimsData.q081,FIq_Carriers.toQ JFu_ClaimsData.q082,FIq_Carriers.toQ JFu_ClaimsData.q083,FIq_Carriers.toQ JFu_ClaimsData.q084,FIq_Carriers.toQ JFu_ClaimsData.q085],by rfl⟩
theorem expected_value (i : Fin (84#usize).val) : expected i=cells data i := by
  fin_cases i <;> rfl
#print axioms expected_value

theorem value (selected : Selected)
    (run : array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy builder field.QM31.ZERO
      JFu_TerminalCallback.claims=ok selected) : selected=data := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact selected.property.trans data.property.symm
  · intro n hn hdata
    exact (JGl_SelectedCells.value selected run ⟨n,by simpa [selected.property] using hn⟩).trans
      (expected_value ⟨n,by simpa [selected.property] using hn⟩)
#print axioms value
end AspisR1.JGl_ConcreteSelected
end
