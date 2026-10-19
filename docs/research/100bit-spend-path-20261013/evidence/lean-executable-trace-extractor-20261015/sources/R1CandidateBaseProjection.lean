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
set_option maxRecDepth 4096

namespace AspisR1.CandidateBaseProjection

open AspisPool.AlgorithmicCircleDecoderV7
open AspisV8R15.ExactTowerBase
open AspisWideTower

attribute [local irreducible] AspisR1.ConcreteBinding.candidates

def recoveredWord
    (eK : QM31Exact →+* WideExact)
    (c1Packed : Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (c2Packed : Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte)) :
    Fin 29 → InitialWord WideExact :=
  AspisR1.TypedRecoveredWords.word AspisR1.ExactBaseProjection.embed eK
    c1Packed c2Packed

theorem rows_base_typed_of_uniform
    {E : Type} [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod AspisCircleGroupOrder.P) E]
    (S : Fin 29 → Subfield E) (F : Subfield E)
    (lanesF : ∀ l : Fin 29, l.val < 26 → S l = F)
    (W : Fin 29 → InitialWord E)
    (typed : AspisR1.CandidateDescent.WordTyped S W)
    (t : AspisR1.ConcreteBinding.Tuple E)
    (ht : t ∈ AspisR1.ConcreteBinding.candidates W)
    (π : Fin 1024 ≃ Fin 1024) :
    R0P.BaseTyped F (R0P.SemSource.rowsOf π t) := by
  have hrows := AspisR1.CandidateDescent.candidate_rows_typed S W typed t ht π
  intro c hc r
  change t c (π r) ∈ F
  rw [← lanesF c hc]
  exact hrows c r

theorem rows_base_typed
    (eK : QM31Exact →+* WideExact)
    (c1Packed : Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (c2Packed : Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (t : AspisR1.ConcreteBinding.Tuple WideExact)
    (ht : t ∈ AspisR1.ConcreteBinding.candidates
      (recoveredWord eK c1Packed c2Packed)) :
    R0P.BaseTyped AspisR1.ExactBaseProjection.embed.fieldRange
      (R0P.SemSource.rowsOf AspisR1.rowEquiv t) := by
  let S := AspisR1.TypedRecoveredWords.laneSubfield
    AspisR1.ExactBaseProjection.embed eK
  let W := recoveredWord eK c1Packed c2Packed
  have htyped : AspisR1.CandidateDescent.WordTyped S W :=
    AspisR1.TypedRecoveredWords.word_typed
      AspisR1.ExactBaseProjection.embed eK c1Packed c2Packed
  have hlanes : ∀ l : Fin 29, l.val < 26 → S l =
      AspisR1.ExactBaseProjection.embed.fieldRange := by
    intro l hl
    simp [S, AspisR1.TypedRecoveredWords.laneSubfield, hl]
  exact rows_base_typed_of_uniform (E := WideExact) S
    AspisR1.ExactBaseProjection.embed.fieldRange hlanes W htyped t ht
    AspisR1.rowEquiv

theorem rows_project
    (eK : QM31Exact →+* WideExact)
    (c1Packed : Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (c2Packed : Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (t : AspisR1.ConcreteBinding.Tuple WideExact)
    (ht : t ∈ AspisR1.ConcreteBinding.candidates
      (recoveredWord eK c1Packed c2Packed))
    (c : Fin 29) (hc : c.val < 26) (r : Fin 1024) :
    AspisR1.ExactBaseProjection.embed
        (AspisR1.ExactBaseProjection.project
          ((R0P.SemSource.rowsOf AspisR1.rowEquiv t) c r)) =
      (R0P.SemSource.rowsOf AspisR1.rowEquiv t) c r := by
  exact AspisR1.ExactBaseProjection.embed_project_of_mem_fieldRange
    (rows_base_typed eK c1Packed c2Packed t ht c hc r)

#print axioms rows_base_typed
#print axioms rows_project
#print axioms rows_base_typed_of_uniform

end AspisR1.CandidateBaseProjection
