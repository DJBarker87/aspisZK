import R1CandidateDescent
import R1TypedRecoveredWords
import R1ExactBaseProjection
import R1D18Transport
import R0P.SemView

/-! Candidate membership and recovered-word typing imply base-field typing
of the transported semantic rows. This is a model-level bridge only; it does
not connect parsed source bytes to the candidate tuple or preserve a spend
relation under arbitrary scalar maps. -/
set_option autoImplicit false

namespace AspisR1.CandidateBaseProjection

open AspisPool.AlgorithmicCircleDecoderV7
open AspisV8R15.ExactTowerBase
open AspisWideTower

theorem rows_base_typed
    (eK : QM31Exact →+* WideExact)
    (c1Packed : Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (c2Packed : Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (t : AspisR1.ConcreteBinding.Tuple WideExact)
    (ht : t ∈ AspisR1.ConcreteBinding.candidates
      (AspisR1.TypedRecoveredWords.word AspisR1.ExactBaseProjection.embed eK
        c1Packed c2Packed)) :
    R0P.BaseTyped AspisR1.ExactBaseProjection.embed.fieldRange
      (R0P.SemSource.rowsOf AspisR1.rowEquiv t) := by
  have htyped := AspisR1.TypedRecoveredWords.word_typed
    AspisR1.ExactBaseProjection.embed eK c1Packed c2Packed
  have hrows := AspisR1.CandidateDescent.candidate_rows_typed
    (AspisR1.TypedRecoveredWords.laneSubfield AspisR1.ExactBaseProjection.embed eK)
    (AspisR1.TypedRecoveredWords.word AspisR1.ExactBaseProjection.embed eK
      c1Packed c2Packed)
    htyped t ht AspisR1.rowEquiv
  intro c hc r
  change t c (AspisR1.rowEquiv r) ∈ AspisR1.ExactBaseProjection.embed.fieldRange
  have h := hrows c r
  simpa [AspisR1.TypedRecoveredWords.laneSubfield, hc] using h

theorem rows_project
    (eK : QM31Exact →+* WideExact)
    (c1Packed : Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (c2Packed : Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (t : AspisR1.ConcreteBinding.Tuple WideExact)
    (ht : t ∈ AspisR1.ConcreteBinding.candidates
      (AspisR1.TypedRecoveredWords.word AspisR1.ExactBaseProjection.embed eK
        c1Packed c2Packed))
    (c : Fin 29) (hc : c.val < 26) (r : Fin 1024) :
    AspisR1.ExactBaseProjection.embed
        (AspisR1.ExactBaseProjection.project
          ((R0P.SemSource.rowsOf AspisR1.rowEquiv t) c r)) =
      (R0P.SemSource.rowsOf AspisR1.rowEquiv t) c r := by
  exact AspisR1.ExactBaseProjection.embed_project_of_mem_fieldRange
    (rows_base_typed eK c1Packed c2Packed t ht c hc r)

#print axioms rows_base_typed
#print axioms rows_project

end AspisR1.CandidateBaseProjection
