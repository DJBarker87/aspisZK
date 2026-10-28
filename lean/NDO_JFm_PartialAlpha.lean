import NDO_JFm_Coordinates
import NDO_JFm_HornerAlpha
import NDO_JFr_RealRounds
set_option autoImplicit false
namespace AspisR1.JFm_PartialAlpha
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
def a00 : Array MainQM 10#usize := Array.repeat 10#usize aspis_core.field.QM31.ZERO
def a01 : Array MainQM 10#usize := ⟨[JFm_Coordinates.value15,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def a02 : Array MainQM 10#usize := ⟨[JFm_Coordinates.value15,JFm_Coordinates.value16,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def a03 : Array MainQM 10#usize := ⟨[JFm_Coordinates.value15,JFm_Coordinates.value16,JFm_Coordinates.value17,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def a04 : Array MainQM 10#usize := ⟨[JFm_Coordinates.value15,JFm_Coordinates.value16,JFm_Coordinates.value17,JFm_Coordinates.value18,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def a05 : Array MainQM 10#usize := ⟨[JFm_Coordinates.value15,JFm_Coordinates.value16,JFm_Coordinates.value17,JFm_Coordinates.value18,JFm_Coordinates.value19,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def a06 : Array MainQM 10#usize := ⟨[JFm_Coordinates.value15,JFm_Coordinates.value16,JFm_Coordinates.value17,JFm_Coordinates.value18,JFm_Coordinates.value19,JFm_Coordinates.value20,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def a07 : Array MainQM 10#usize := ⟨[JFm_Coordinates.value15,JFm_Coordinates.value16,JFm_Coordinates.value17,JFm_Coordinates.value18,JFm_Coordinates.value19,JFm_Coordinates.value20,JFm_Coordinates.value21,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def a08 : Array MainQM 10#usize := ⟨[JFm_Coordinates.value15,JFm_Coordinates.value16,JFm_Coordinates.value17,JFm_Coordinates.value18,JFm_Coordinates.value19,JFm_Coordinates.value20,JFm_Coordinates.value21,JFm_Coordinates.value22,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def a09 : Array MainQM 10#usize := ⟨[JFm_Coordinates.value15,JFm_Coordinates.value16,JFm_Coordinates.value17,JFm_Coordinates.value18,JFm_Coordinates.value19,JFm_Coordinates.value20,JFm_Coordinates.value21,JFm_Coordinates.value22,JFm_Coordinates.value23,aspis_core.field.QM31.ZERO],by rfl⟩
def a10 : Array MainQM 10#usize := ⟨[JFm_Coordinates.value15,JFm_Coordinates.value16,JFm_Coordinates.value17,JFm_Coordinates.value18,JFm_Coordinates.value19,JFm_Coordinates.value20,JFm_Coordinates.value21,JFm_Coordinates.value22,JFm_Coordinates.value23,JFm_Coordinates.value24],by rfl⟩
theorem full : a10=JFr_Round00.challenges := by rfl
#print axioms full
theorem update00 : Array.update a00 0#usize JFm_Coordinates.value15=ok a01 := by rfl
#print axioms update00
theorem horner00 : AspisR1SemanticCallExtraction.r1_semantic.semantic_value JFr_Data00.p
    (mainAlphaArrayToGen a01) 0#usize=ok JFr_Data00.output := by
  have joined := JFr_HornerTrace.append JFr_Horner00_0.trace JFr_Horner00_1.trace
  have moved := JFm_HornerAlpha.transport (b := mainAlphaArrayToGen a01) joined (by rfl)
  have zero : JFr_Horner00_0.initial=AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
    unfold JFr_Horner00_0.initial JFr_WordArithmetic.q AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO
    rfl
  have last : JFr_Horner00_1.final=JFr_Data00.output := rfl
  rw [zero,last] at moved
  exact JFr_HornerTrace.source moved (by change ¬(0:Nat)>0;omega)
#print axioms horner00
theorem value00 : generatedMainValue JFr_Round00.polynomial a01 0#usize=
    ok (genToMain JFr_Data00.output) := by
  unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
  have same : mainArrayToGen JFr_Round00.polynomial=JFr_Data00.p := rfl
  rw [same,horner00]
  rfl
#print axioms value00
theorem update01 : Array.update a01 1#usize JFm_Coordinates.value16=ok a02 := by rfl
#print axioms update01
theorem horner01 : AspisR1SemanticCallExtraction.r1_semantic.semantic_value JFr_Data01.p
    (mainAlphaArrayToGen a02) 1#usize=ok JFr_Data01.output := by
  have joined := JFr_HornerTrace.append JFr_Horner01_0.trace JFr_Horner01_1.trace
  have moved := JFm_HornerAlpha.transport (b := mainAlphaArrayToGen a02) joined (by rfl)
  have zero : JFr_Horner01_0.initial=AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
    unfold JFr_Horner01_0.initial JFr_WordArithmetic.q AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO
    rfl
  have last : JFr_Horner01_1.final=JFr_Data01.output := rfl
  rw [zero,last] at moved
  exact JFr_HornerTrace.source moved (by change ¬(0:Nat)>0;omega)
#print axioms horner01
theorem value01 : generatedMainValue JFr_Round01.polynomial a02 1#usize=
    ok (genToMain JFr_Data01.output) := by
  unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
  have same : mainArrayToGen JFr_Round01.polynomial=JFr_Data01.p := rfl
  rw [same,horner01]
  rfl
#print axioms value01
theorem update02 : Array.update a02 2#usize JFm_Coordinates.value17=ok a03 := by rfl
#print axioms update02
theorem horner02 : AspisR1SemanticCallExtraction.r1_semantic.semantic_value JFr_Data02.p
    (mainAlphaArrayToGen a03) 2#usize=ok JFr_Data02.output := by
  have joined := JFr_HornerTrace.append JFr_Horner02_0.trace JFr_Horner02_1.trace
  have moved := JFm_HornerAlpha.transport (b := mainAlphaArrayToGen a03) joined (by rfl)
  have zero : JFr_Horner02_0.initial=AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
    unfold JFr_Horner02_0.initial JFr_WordArithmetic.q AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO
    rfl
  have last : JFr_Horner02_1.final=JFr_Data02.output := rfl
  rw [zero,last] at moved
  exact JFr_HornerTrace.source moved (by change ¬(0:Nat)>0;omega)
#print axioms horner02
theorem value02 : generatedMainValue JFr_Round02.polynomial a03 2#usize=
    ok (genToMain JFr_Data02.output) := by
  unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
  have same : mainArrayToGen JFr_Round02.polynomial=JFr_Data02.p := rfl
  rw [same,horner02]
  rfl
#print axioms value02
theorem update03 : Array.update a03 3#usize JFm_Coordinates.value18=ok a04 := by rfl
#print axioms update03
theorem horner03 : AspisR1SemanticCallExtraction.r1_semantic.semantic_value JFr_Data03.p
    (mainAlphaArrayToGen a04) 3#usize=ok JFr_Data03.output := by
  have joined := JFr_HornerTrace.append JFr_Horner03_0.trace JFr_Horner03_1.trace
  have moved := JFm_HornerAlpha.transport (b := mainAlphaArrayToGen a04) joined (by rfl)
  have zero : JFr_Horner03_0.initial=AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
    unfold JFr_Horner03_0.initial JFr_WordArithmetic.q AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO
    rfl
  have last : JFr_Horner03_1.final=JFr_Data03.output := rfl
  rw [zero,last] at moved
  exact JFr_HornerTrace.source moved (by change ¬(0:Nat)>0;omega)
#print axioms horner03
theorem value03 : generatedMainValue JFr_Round03.polynomial a04 3#usize=
    ok (genToMain JFr_Data03.output) := by
  unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
  have same : mainArrayToGen JFr_Round03.polynomial=JFr_Data03.p := rfl
  rw [same,horner03]
  rfl
#print axioms value03
theorem update04 : Array.update a04 4#usize JFm_Coordinates.value19=ok a05 := by rfl
#print axioms update04
theorem horner04 : AspisR1SemanticCallExtraction.r1_semantic.semantic_value JFr_Data04.p
    (mainAlphaArrayToGen a05) 4#usize=ok JFr_Data04.output := by
  have joined := JFr_HornerTrace.append JFr_Horner04_0.trace JFr_Horner04_1.trace
  have moved := JFm_HornerAlpha.transport (b := mainAlphaArrayToGen a05) joined (by rfl)
  have zero : JFr_Horner04_0.initial=AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
    unfold JFr_Horner04_0.initial JFr_WordArithmetic.q AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO
    rfl
  have last : JFr_Horner04_1.final=JFr_Data04.output := rfl
  rw [zero,last] at moved
  exact JFr_HornerTrace.source moved (by change ¬(0:Nat)>0;omega)
#print axioms horner04
theorem value04 : generatedMainValue JFr_Round04.polynomial a05 4#usize=
    ok (genToMain JFr_Data04.output) := by
  unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
  have same : mainArrayToGen JFr_Round04.polynomial=JFr_Data04.p := rfl
  rw [same,horner04]
  rfl
#print axioms value04
theorem update05 : Array.update a05 5#usize JFm_Coordinates.value20=ok a06 := by rfl
#print axioms update05
theorem horner05 : AspisR1SemanticCallExtraction.r1_semantic.semantic_value JFr_Data05.p
    (mainAlphaArrayToGen a06) 5#usize=ok JFr_Data05.output := by
  have joined := JFr_HornerTrace.append JFr_Horner05_0.trace JFr_Horner05_1.trace
  have moved := JFm_HornerAlpha.transport (b := mainAlphaArrayToGen a06) joined (by rfl)
  have zero : JFr_Horner05_0.initial=AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
    unfold JFr_Horner05_0.initial JFr_WordArithmetic.q AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO
    rfl
  have last : JFr_Horner05_1.final=JFr_Data05.output := rfl
  rw [zero,last] at moved
  exact JFr_HornerTrace.source moved (by change ¬(0:Nat)>0;omega)
#print axioms horner05
theorem value05 : generatedMainValue JFr_Round05.polynomial a06 5#usize=
    ok (genToMain JFr_Data05.output) := by
  unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
  have same : mainArrayToGen JFr_Round05.polynomial=JFr_Data05.p := rfl
  rw [same,horner05]
  rfl
#print axioms value05
theorem update06 : Array.update a06 6#usize JFm_Coordinates.value21=ok a07 := by rfl
#print axioms update06
theorem horner06 : AspisR1SemanticCallExtraction.r1_semantic.semantic_value JFr_Data06.p
    (mainAlphaArrayToGen a07) 6#usize=ok JFr_Data06.output := by
  have joined := JFr_HornerTrace.append JFr_Horner06_0.trace JFr_Horner06_1.trace
  have moved := JFm_HornerAlpha.transport (b := mainAlphaArrayToGen a07) joined (by rfl)
  have zero : JFr_Horner06_0.initial=AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
    unfold JFr_Horner06_0.initial JFr_WordArithmetic.q AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO
    rfl
  have last : JFr_Horner06_1.final=JFr_Data06.output := rfl
  rw [zero,last] at moved
  exact JFr_HornerTrace.source moved (by change ¬(0:Nat)>0;omega)
#print axioms horner06
theorem value06 : generatedMainValue JFr_Round06.polynomial a07 6#usize=
    ok (genToMain JFr_Data06.output) := by
  unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
  have same : mainArrayToGen JFr_Round06.polynomial=JFr_Data06.p := rfl
  rw [same,horner06]
  rfl
#print axioms value06
theorem update07 : Array.update a07 7#usize JFm_Coordinates.value22=ok a08 := by rfl
#print axioms update07
theorem horner07 : AspisR1SemanticCallExtraction.r1_semantic.semantic_value JFr_Data07.p
    (mainAlphaArrayToGen a08) 7#usize=ok JFr_Data07.output := by
  have joined := JFr_HornerTrace.append JFr_Horner07_0.trace JFr_Horner07_1.trace
  have moved := JFm_HornerAlpha.transport (b := mainAlphaArrayToGen a08) joined (by rfl)
  have zero : JFr_Horner07_0.initial=AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
    unfold JFr_Horner07_0.initial JFr_WordArithmetic.q AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO
    rfl
  have last : JFr_Horner07_1.final=JFr_Data07.output := rfl
  rw [zero,last] at moved
  exact JFr_HornerTrace.source moved (by change ¬(0:Nat)>0;omega)
#print axioms horner07
theorem value07 : generatedMainValue JFr_Round07.polynomial a08 7#usize=
    ok (genToMain JFr_Data07.output) := by
  unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
  have same : mainArrayToGen JFr_Round07.polynomial=JFr_Data07.p := rfl
  rw [same,horner07]
  rfl
#print axioms value07
theorem update08 : Array.update a08 8#usize JFm_Coordinates.value23=ok a09 := by rfl
#print axioms update08
theorem horner08 : AspisR1SemanticCallExtraction.r1_semantic.semantic_value JFr_Data08.p
    (mainAlphaArrayToGen a09) 8#usize=ok JFr_Data08.output := by
  have joined := JFr_HornerTrace.append JFr_Horner08_0.trace JFr_Horner08_1.trace
  have moved := JFm_HornerAlpha.transport (b := mainAlphaArrayToGen a09) joined (by rfl)
  have zero : JFr_Horner08_0.initial=AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
    unfold JFr_Horner08_0.initial JFr_WordArithmetic.q AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO
    rfl
  have last : JFr_Horner08_1.final=JFr_Data08.output := rfl
  rw [zero,last] at moved
  exact JFr_HornerTrace.source moved (by change ¬(0:Nat)>0;omega)
#print axioms horner08
theorem value08 : generatedMainValue JFr_Round08.polynomial a09 8#usize=
    ok (genToMain JFr_Data08.output) := by
  unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
  have same : mainArrayToGen JFr_Round08.polynomial=JFr_Data08.p := rfl
  rw [same,horner08]
  rfl
#print axioms value08
theorem update09 : Array.update a09 9#usize JFm_Coordinates.value24=ok a10 := by rfl
#print axioms update09
theorem horner09 : AspisR1SemanticCallExtraction.r1_semantic.semantic_value JFr_Data09.p
    (mainAlphaArrayToGen a10) 9#usize=ok JFr_Data09.output := by
  have joined := JFr_HornerTrace.append JFr_Horner09_0.trace JFr_Horner09_1.trace
  have moved := JFm_HornerAlpha.transport (b := mainAlphaArrayToGen a10) joined (by rfl)
  have zero : JFr_Horner09_0.initial=AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
    unfold JFr_Horner09_0.initial JFr_WordArithmetic.q AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO
    rfl
  have last : JFr_Horner09_1.final=JFr_Data09.output := rfl
  rw [zero,last] at moved
  exact JFr_HornerTrace.source moved (by change ¬(0:Nat)>0;omega)
#print axioms horner09
theorem value09 : generatedMainValue JFr_Round09.polynomial a10 9#usize=
    ok (genToMain JFr_Data09.output) := by
  unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
  have same : mainArrayToGen JFr_Round09.polynomial=JFr_Data09.p := rfl
  rw [same,horner09]
  rfl
#print axioms value09
end AspisR1.JFm_PartialAlpha
