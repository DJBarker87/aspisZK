import RPu_FJs_LiteralRows
import RPv_FJr_BodyPairMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_PreparedPoint
open Aeneas Aeneas.Std Result
open CheckpointBytes4ReaderFields
abbrev K := OraclePortCheckpointAbiC5.K

theorem decode (x : K) :
    FJc_WeightValues.decode (FIn_WeightsInstall.toQ (sourceK x))=x := by
  change CheckpointBytes5Output.ofK (sourceK x)=x
  exact CheckpointBytes5Output.ofK_source x

theorem point (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am) (j : Fin 10) :
    FJs_LiteralRows.point p.semantic_alpha j=pm.semanticAlpha j := by
  unfold FJs_LiteralRows.point FJf_ModelPoint.decoded FJc_WeightArray.value
  change (match (p.semantic_alpha.val.map FIn_WeightsInstall.toQ)[j.val]? with
    | some x=>FJc_WeightValues.decode x | none=>0)=_
  rw [fields.semantic]
  simp only [List.map_map,List.getElem?_map,List.getElem?_ofFn,j.isLt,↓reduceDIte,Option.map_some]
  exact decode _

#print axioms decode
#print axioms point
end AspisR1.FJs_PreparedPoint
end
