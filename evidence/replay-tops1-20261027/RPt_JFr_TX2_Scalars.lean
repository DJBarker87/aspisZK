import RPt_JFr_TX2_Slot10_0
import RPt_JFr_TX2_Slot10_1
import RPt_JFr_TX2_Slot10_2
import RPt_JFr_TX2_Slot10_3
import RPt_JFr_TX2_Slot11_0
import RPt_JFr_TX2_Slot11_1
import RPt_JFr_TX2_Slot11_2
import RPt_JFr_TX2_Slot11_3
import RPt_JFr_TX2_Slot12_0
import RPt_JFr_TX2_Slot12_1
import RPt_JFr_TX2_Slot12_2
import RPt_JFr_TX2_Slot12_3
import RPt_JFr_TX2_Slot13_0
import RPt_JFr_TX2_Slot13_1
import RPt_JFr_TX2_Slot13_2
import RPt_JFr_TX2_Slot13_3
import RPt_JFr_TX2_Slot14_0
import RPt_JFr_TX2_Slot14_1
import RPt_JFr_TX2_Slot14_2
import RPt_JFr_TX2_Slot14_3
import RPt_JFr_TX2_Slot15_0
import RPt_JFr_TX2_Slot15_1
import RPt_JFr_TX2_Slot15_2
import RPt_JFr_TX2_Slot15_3
import RPt_JFr_TX2_Slot16_0
import RPt_JFr_TX2_Slot16_1
import RPt_JFr_TX2_Slot16_2
import RPt_JFr_TX2_Slot16_3
import RPt_JFr_TX2_Slot17_0
import RPt_JFr_TX2_Slot17_1
import RPt_JFr_TX2_Slot17_2
import RPt_JFr_TX2_Slot17_3
import RPt_JFr_TX2_Slot18_0
import RPt_JFr_TX2_Slot18_1
import RPt_JFr_TX2_Slot18_2
import RPt_JFr_TX2_Slot18_3
import RPt_JFr_TX2_Slot19_0
import RPt_JFr_TX2_Slot19_1
import RPt_JFr_TX2_Slot19_2
import RPt_JFr_TX2_Slot19_3
import RPt_JFr_TX2_Slot20_0
import RPt_JFr_TX2_Slot20_1
import RPt_JFr_TX2_Slot20_2
import RPt_JFr_TX2_Slot20_3
import RPt_JFr_TX2_Slot21_0
import RPt_JFr_TX2_Slot21_1
import RPt_JFr_TX2_Slot21_2
import RPt_JFr_TX2_Slot21_3
import RPt_JFr_TX2_ScalarCanon
import RPt_JFn_Values
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_Scalars
open Aeneas Aeneas.Std Result

def values (i : Fin 12) (slot : Fin 4) : Array U32 26#usize :=
  match i.val,slot.val with
  | 0,0 => JFr_TX2_Slot10_0.values
  | 0,1 => JFr_TX2_Slot10_1.values
  | 0,2 => JFr_TX2_Slot10_2.values
  | 0,3 => JFr_TX2_Slot10_3.values
  | 1,0 => JFr_TX2_Slot11_0.values
  | 1,1 => JFr_TX2_Slot11_1.values
  | 1,2 => JFr_TX2_Slot11_2.values
  | 1,3 => JFr_TX2_Slot11_3.values
  | 2,0 => JFr_TX2_Slot12_0.values
  | 2,1 => JFr_TX2_Slot12_1.values
  | 2,2 => JFr_TX2_Slot12_2.values
  | 2,3 => JFr_TX2_Slot12_3.values
  | 3,0 => JFr_TX2_Slot13_0.values
  | 3,1 => JFr_TX2_Slot13_1.values
  | 3,2 => JFr_TX2_Slot13_2.values
  | 3,3 => JFr_TX2_Slot13_3.values
  | 4,0 => JFr_TX2_Slot14_0.values
  | 4,1 => JFr_TX2_Slot14_1.values
  | 4,2 => JFr_TX2_Slot14_2.values
  | 4,3 => JFr_TX2_Slot14_3.values
  | 5,0 => JFr_TX2_Slot15_0.values
  | 5,1 => JFr_TX2_Slot15_1.values
  | 5,2 => JFr_TX2_Slot15_2.values
  | 5,3 => JFr_TX2_Slot15_3.values
  | 6,0 => JFr_TX2_Slot16_0.values
  | 6,1 => JFr_TX2_Slot16_1.values
  | 6,2 => JFr_TX2_Slot16_2.values
  | 6,3 => JFr_TX2_Slot16_3.values
  | 7,0 => JFr_TX2_Slot17_0.values
  | 7,1 => JFr_TX2_Slot17_1.values
  | 7,2 => JFr_TX2_Slot17_2.values
  | 7,3 => JFr_TX2_Slot17_3.values
  | 8,0 => JFr_TX2_Slot18_0.values
  | 8,1 => JFr_TX2_Slot18_1.values
  | 8,2 => JFr_TX2_Slot18_2.values
  | 8,3 => JFr_TX2_Slot18_3.values
  | 9,0 => JFr_TX2_Slot19_0.values
  | 9,1 => JFr_TX2_Slot19_1.values
  | 9,2 => JFr_TX2_Slot19_2.values
  | 9,3 => JFr_TX2_Slot19_3.values
  | 10,0 => JFr_TX2_Slot20_0.values
  | 10,1 => JFr_TX2_Slot20_1.values
  | 10,2 => JFr_TX2_Slot20_2.values
  | 10,3 => JFr_TX2_Slot20_3.values
  | 11,0 => JFr_TX2_Slot21_0.values
  | 11,1 => JFr_TX2_Slot21_1.values
  | 11,2 => JFr_TX2_Slot21_2.values
  | 11,3 => JFr_TX2_Slot21_3.values
  | _,_ => Array.repeat 26#usize 0#u32

theorem source (i : Fin 12) (slot : Fin 4) (term : Fin 26) :
    JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array (JFn_Values.position i))
      (Usize.ofNat slot.val (by have := slot.isLt;scalar_tac))
      (Usize.ofNat term.val (by have := term.isLt;scalar_tac))=
        ok ((values i slot).val[term.val]'(by rw [(values i slot).property];exact term.isLt)) := by
  fin_cases i
  · fin_cases slot
    · exact JFr_TX2_Slot10_0.source term
    · exact JFr_TX2_Slot10_1.source term
    · exact JFr_TX2_Slot10_2.source term
    · exact JFr_TX2_Slot10_3.source term
  · fin_cases slot
    · exact JFr_TX2_Slot11_0.source term
    · exact JFr_TX2_Slot11_1.source term
    · exact JFr_TX2_Slot11_2.source term
    · exact JFr_TX2_Slot11_3.source term
  · fin_cases slot
    · exact JFr_TX2_Slot12_0.source term
    · exact JFr_TX2_Slot12_1.source term
    · exact JFr_TX2_Slot12_2.source term
    · exact JFr_TX2_Slot12_3.source term
  · fin_cases slot
    · exact JFr_TX2_Slot13_0.source term
    · exact JFr_TX2_Slot13_1.source term
    · exact JFr_TX2_Slot13_2.source term
    · exact JFr_TX2_Slot13_3.source term
  · fin_cases slot
    · exact JFr_TX2_Slot14_0.source term
    · exact JFr_TX2_Slot14_1.source term
    · exact JFr_TX2_Slot14_2.source term
    · exact JFr_TX2_Slot14_3.source term
  · fin_cases slot
    · exact JFr_TX2_Slot15_0.source term
    · exact JFr_TX2_Slot15_1.source term
    · exact JFr_TX2_Slot15_2.source term
    · exact JFr_TX2_Slot15_3.source term
  · fin_cases slot
    · exact JFr_TX2_Slot16_0.source term
    · exact JFr_TX2_Slot16_1.source term
    · exact JFr_TX2_Slot16_2.source term
    · exact JFr_TX2_Slot16_3.source term
  · fin_cases slot
    · exact JFr_TX2_Slot17_0.source term
    · exact JFr_TX2_Slot17_1.source term
    · exact JFr_TX2_Slot17_2.source term
    · exact JFr_TX2_Slot17_3.source term
  · fin_cases slot
    · exact JFr_TX2_Slot18_0.source term
    · exact JFr_TX2_Slot18_1.source term
    · exact JFr_TX2_Slot18_2.source term
    · exact JFr_TX2_Slot18_3.source term
  · fin_cases slot
    · exact JFr_TX2_Slot19_0.source term
    · exact JFr_TX2_Slot19_1.source term
    · exact JFr_TX2_Slot19_2.source term
    · exact JFr_TX2_Slot19_3.source term
  · fin_cases slot
    · exact JFr_TX2_Slot20_0.source term
    · exact JFr_TX2_Slot20_1.source term
    · exact JFr_TX2_Slot20_2.source term
    · exact JFr_TX2_Slot20_3.source term
  · fin_cases slot
    · exact JFr_TX2_Slot21_0.source term
    · exact JFr_TX2_Slot21_1.source term
    · exact JFr_TX2_Slot21_2.source term
    · exact JFr_TX2_Slot21_3.source term

theorem canonical (i : Fin 12) (slot : Fin 4) (term : Fin 26) :
    ((values i slot).val[term.val]'(by rw [(values i slot).property];exact term.isLt)).val<2147483647 := by
  fin_cases i
  · fin_cases slot
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot10_0.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot10_1.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot10_2.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot10_3.decode term)
  · fin_cases slot
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot11_0.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot11_1.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot11_2.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot11_3.decode term)
  · fin_cases slot
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot12_0.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot12_1.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot12_2.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot12_3.decode term)
  · fin_cases slot
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot13_0.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot13_1.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot13_2.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot13_3.decode term)
  · fin_cases slot
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot14_0.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot14_1.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot14_2.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot14_3.decode term)
  · fin_cases slot
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot15_0.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot15_1.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot15_2.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot15_3.decode term)
  · fin_cases slot
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot16_0.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot16_1.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot16_2.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot16_3.decode term)
  · fin_cases slot
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot17_0.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot17_1.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot17_2.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot17_3.decode term)
  · fin_cases slot
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot18_0.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot18_1.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot18_2.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot18_3.decode term)
  · fin_cases slot
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot19_0.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot19_1.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot19_2.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot19_3.decode term)
  · fin_cases slot
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot20_0.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot20_1.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot20_2.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot20_3.decode term)
  · fin_cases slot
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot21_0.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot21_1.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot21_2.decode term)
    · exact JFr_TX2_ScalarCanon.source _ _ (JFr_TX2_Slot21_3.decode term)

#print axioms source
#print axioms canonical
end AspisR1.JFr_TX2_Scalars
end
