import SAP_CurrentNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_NumericFields
open AspisR1CurrentCaller.InstalledPreparation
open AspisR1ClaimPreparedBridge

theorem alpha (out : AspisR1PublicPreparation.verifier.Prepared) (j : Fin 2) :
    SAP_CurrentNumeric.alpha (currentPrepared out) j = currentE (F3L_SourcePrepared.alpha out j) := by
  simp only [SAP_CurrentNumeric.alpha,F3L_SourcePrepared.alpha,currentPrepared,mapArray,List.getElem_map]

theorem semanticAlpha (out : AspisR1PublicPreparation.verifier.Prepared) (j : Fin 10) :
    SAP_CurrentNumeric.semanticAlpha (currentPrepared out) j = currentQ (F3L_SourcePrepared.semanticAlpha out j) := by
  simp only [SAP_CurrentNumeric.semanticAlpha,F3L_SourcePrepared.semanticAlpha,currentPrepared,mapArray,List.getElem_map]

theorem coordinate (out : AspisR1PublicPreparation.verifier.Prepared) (j : Fin 4) :
    SAP_CurrentNumeric.coordinate (currentPrepared out) j = currentQ (F3L_SourcePrepared.coordinate out j) := by
  fin_cases j <;> simp only [SAP_CurrentNumeric.coordinate,SAP_CurrentNumeric.point,
    F3L_SourcePrepared.coordinate,F3L_SourcePrepared.point,currentPrepared,mapArray,List.getElem_map]
  all_goals rfl

#print axioms alpha
#print axioms semanticAlpha
#print axioms coordinate
end AspisR1.SAP_NumericFields
end
