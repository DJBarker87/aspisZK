import NDO_JHm_Row26_00
import NDO_JHm_Row26_10
import NDO_JHm_Row26_20
import NDO_JHm_RowFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_Row26Numeric
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisS1ExtractedRoundChildren
theorem cell (out : Array aspis_core.field.QM31 29#usize)
    (call : decodeMain 29#usize JFu_Q26Source.record 0#usize=ok (.Ok out)) (j : Fin 29) :
    JHm_RowFacts.scalar (out.val[j.val]'(by have h:=out.property;change out.val.length=29 at h;omega))=
    (JHm_Arithmetic.row 4)[j.val]'(by rw [(show (JHm_Arithmetic.row 4).length=29 from rfl)];exact j.isLt) := by
  fin_cases j
  · rw [JHm_Row26_00.source00 out call];rfl
  · rw [JHm_Row26_00.source01 out call];rfl
  · rw [JHm_Row26_00.source02 out call];rfl
  · rw [JHm_Row26_00.source03 out call];rfl
  · rw [JHm_Row26_00.source04 out call];rfl
  · rw [JHm_Row26_00.source05 out call];rfl
  · rw [JHm_Row26_00.source06 out call];rfl
  · rw [JHm_Row26_00.source07 out call];rfl
  · rw [JHm_Row26_00.source08 out call];rfl
  · rw [JHm_Row26_00.source09 out call];rfl
  · rw [JHm_Row26_10.source10 out call];rfl
  · rw [JHm_Row26_10.source11 out call];rfl
  · rw [JHm_Row26_10.source12 out call];rfl
  · rw [JHm_Row26_10.source13 out call];rfl
  · rw [JHm_Row26_10.source14 out call];rfl
  · rw [JHm_Row26_10.source15 out call];rfl
  · rw [JHm_Row26_10.source16 out call];rfl
  · rw [JHm_Row26_10.source17 out call];rfl
  · rw [JHm_Row26_10.source18 out call];rfl
  · rw [JHm_Row26_10.source19 out call];rfl
  · rw [JHm_Row26_20.source20 out call];rfl
  · rw [JHm_Row26_20.source21 out call];rfl
  · rw [JHm_Row26_20.source22 out call];rfl
  · rw [JHm_Row26_20.source23 out call];rfl
  · rw [JHm_Row26_20.source24 out call];rfl
  · rw [JHm_Row26_20.source25 out call];rfl
  · rw [JHm_Row26_20.source26 out call];rfl
  · rw [JHm_Row26_20.source27 out call];rfl
  · rw [JHm_Row26_20.source28 out call];rfl
#print axioms cell
theorem source (out : Array aspis_core.field.QM31 29#usize)
    (call : decodeMain 29#usize JFu_Q26Source.record 0#usize=ok (.Ok out)) :
    out.val.map JHm_RowFacts.scalar=JHm_Arithmetic.row 4 := by
  apply List.ext_getElem
  · simp only [List.length_map,out.property,(show (JHm_Arithmetic.row 4).length=29 from rfl)];rfl
  · intro j hj hk
    simp only [List.getElem_map]
    exact cell out call ⟨j,by rw [(show (JHm_Arithmetic.row 4).length=29 from rfl)] at hk;exact hk⟩
#print axioms source
end AspisR1.JHm_Row26Numeric
end
