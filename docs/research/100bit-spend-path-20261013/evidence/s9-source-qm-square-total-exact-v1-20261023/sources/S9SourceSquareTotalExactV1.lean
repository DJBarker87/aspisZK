import S9QMSquareHelperSourceBridgeV1
import S9ResultSuccessReflectionV1
import S3S9ConcreteSquareSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9SourceSquareTotalExactV1

local instance currentFieldOpsForSemantics : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps

abbrev H := AspisR1S9QMSquareHelperSourceBridgeV1.CQ
abbrev X := AspisR1S9QMSquareHelperSourceBridgeV1.XQ
abbrev Sem := AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics
abbrev toCut := AspisR1S9QMSquareHelperSourceBridgeV1.toCut
abbrev fromCut := AspisR1S9QMSquareHelperSourceBridgeV1.fromCut

/-- Totality and exact field semantics of the same extracted square call;
no independent source-success premise is supplied. -/
theorem source_qm_square_total_exact (x : H) (hx : Sem.canonical x) :
    ∃ z : X,
      AspisR1S9SquareMulQMCutV1.field.QM31.square (toCut x) = .ok z ∧
      Sem.canonical (fromCut z) ∧
      Sem.decode (fromCut z) = Sem.decode x * Sem.decode x := by
  have hm := AspisR1S9QMSquareHelperSourceBridgeV1.actual_qm_square_maps_to_installed_helper x hx
  obtain ⟨w, hw, hc, hd⟩ :=
    AspisR1S9ConcreteSquareSemanticsV1.concrete_qmSquare_total x hx
  have ht : AspisR1S9ConcreteFieldOpsV1.actualQMSquare x = .ok w := by
    simpa only [AspisR1S9ConcreteFieldOpsV1.concrete_qmSquare_dispatch] using hw
  exact AspisR1S9ResultSuccessReflectionV1.source_success_of_target
    fromCut (AspisR1S9SquareMulQMCutV1.field.QM31.square (toCut x))
    (AspisR1S9ConcreteFieldOpsV1.actualQMSquare x)
    (fun z => Sem.canonical z ∧ Sem.decode z = Sem.decode x * Sem.decode x)
    hm ⟨w, ht, hc, hd⟩

#print axioms source_qm_square_total_exact

end AspisR1S9SourceSquareTotalExactV1
