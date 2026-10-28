import NDO_JFw_TX2_P28
import NDO_JFv_TX2_HeadFlat
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Coefficients
open Aeneas Aeneas.Std Result
def value (j : Fin 29) : FIo_Install.NE :=
  match j.val with
  | 0 => JFw_TX2_P00.value
  | 1 => JFw_TX2_P01.value
  | 2 => JFw_TX2_P02.value
  | 3 => JFw_TX2_P03.value
  | 4 => JFw_TX2_P04.value
  | 5 => JFw_TX2_P05.value
  | 6 => JFw_TX2_P06.value
  | 7 => JFw_TX2_P07.value
  | 8 => JFw_TX2_P08.value
  | 9 => JFw_TX2_P09.value
  | 10 => JFw_TX2_P10.value
  | 11 => JFw_TX2_P11.value
  | 12 => JFw_TX2_P12.value
  | 13 => JFw_TX2_P13.value
  | 14 => JFw_TX2_P14.value
  | 15 => JFw_TX2_P15.value
  | 16 => JFw_TX2_P16.value
  | 17 => JFw_TX2_P17.value
  | 18 => JFw_TX2_P18.value
  | 19 => JFw_TX2_P19.value
  | 20 => JFw_TX2_P20.value
  | 21 => JFw_TX2_P21.value
  | 22 => JFw_TX2_P22.value
  | 23 => JFw_TX2_P23.value
  | 24 => JFw_TX2_P24.value
  | 25 => JFw_TX2_P25.value
  | 26 => JFw_TX2_P26.value
  | 27 => JFw_TX2_P27.value
  | 28 => JFw_TX2_P28.value
  | _ => JFw_TX2_P00.value

theorem source (j : Fin 29) : JFw_TX2_PowersExplicit.entry j=value j := by
  fin_cases j
  · exact JFw_TX2_P00.source
  · exact JFw_TX2_P01.source
  · exact JFw_TX2_P02.source
  · exact JFw_TX2_P03.source
  · exact JFw_TX2_P04.source
  · exact JFw_TX2_P05.source
  · exact JFw_TX2_P06.source
  · exact JFw_TX2_P07.source
  · exact JFw_TX2_P08.source
  · exact JFw_TX2_P09.source
  · exact JFw_TX2_P10.source
  · exact JFw_TX2_P11.source
  · exact JFw_TX2_P12.source
  · exact JFw_TX2_P13.source
  · exact JFw_TX2_P14.source
  · exact JFw_TX2_P15.source
  · exact JFw_TX2_P16.source
  · exact JFw_TX2_P17.source
  · exact JFw_TX2_P18.source
  · exact JFw_TX2_P19.source
  · exact JFw_TX2_P20.source
  · exact JFw_TX2_P21.source
  · exact JFw_TX2_P22.source
  · exact JFw_TX2_P23.source
  · exact JFw_TX2_P24.source
  · exact JFw_TX2_P25.source
  · exact JFw_TX2_P26.source
  · exact JFw_TX2_P27.source
  · exact JFw_TX2_P28.source

theorem limbs (term : Fin 26) : JFr_TX2_FirstLane.limbs term=
    JFv_TX2_FromLimbsMeaning.limbs (value ⟨term.val,by have:=term.isLt;omega⟩) := by
  have h := source ⟨term.val,by have:=term.isLt;omega⟩
  change JFr_TX2_FirstLane.coefficient term=_ at h
  unfold JFr_TX2_FirstLane.limbs
  rw [h]
  rfl
#print axioms source
#print axioms limbs
end AspisR1.JFw_TX2_Coefficients
end
