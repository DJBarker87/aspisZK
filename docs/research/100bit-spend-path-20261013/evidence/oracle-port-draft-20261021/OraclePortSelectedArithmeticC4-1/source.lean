import OraclePortStoredChecksC4

/-! Arithmetic depends only on queried fibres. A sparse opening completion
need not equal the recovered full words outside those fibres. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortSelectedArithmeticC4
open AspisCircleGroupOrder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6Width29CorrelatedAgreement
variable {E K : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E] [Field K] [Fintype K] [Algebra (ZMod P) K]

def withWords (d : MatchingSupport.Data E) (W : Fin 29 → InitialWord E)
    (V : FinalWord E) : MatchingSupport.Data E := {d with W := W,V := V}

theorem batched_fibre (W W' : Fin 29 → InitialWord E) (gamma : E) (u : Fin 262144)
    (same : ∀ lane, FirstFold.fibre (W lane) u = FirstFold.fibre (W' lane) u) :
    FirstFold.fibre (TwoFoldExtraction.batchedWord W gamma) u =
      FirstFold.fibre (TwoFoldExtraction.batchedWord W' gamma) u := by
  funext slot
  unfold FirstFold.fibre TwoFoldExtraction.batchedWord width29CurveValue
  congr 1
  funext lane
  exact congrFun (same lane) slot

theorem first_fold (f g : InitialWord E) (alpha : E) (u : Fin 262144)
    (same : FirstFold.fibre f u = FirstFold.fibre g u) :
    FirstFold.foldWord alpha f u = FirstFold.foldWord alpha g u := by
  unfold FirstFold.foldWord FirstFold.channels
  rw [same]

theorem first_match (d : MatchingSupport.Data E) (W : Fin 29 → InitialWord E)
    (V : FinalWord E) (u : Fin 262144)
    (initial : ∀ lane, FirstFold.fibre (d.W lane) u = FirstFold.fibre (W lane) u)
    (folded : d.V u = V u) :
    MatchingSupport.match0 d u ↔ MatchingSupport.match0 (withWords d W V) u := by
  unfold MatchingSupport.match0
  change FirstFold.foldWord d.alpha0 (TwoFoldExtraction.batchedWord d.W d.gamma) u = d.V u ↔
    FirstFold.foldWord d.alpha0 (TwoFoldExtraction.batchedWord W d.gamma) u = V u
  rw [first_fold _ _ _ _ (batched_fibre _ _ _ _ initial),folded]

theorem second_value (d : MatchingSupport.Data E) (W : Fin 29 → InitialWord E)
    (V : FinalWord E) (q : Fin 22 → Fin 262144) (j : Fin 22)
    (same : ∀ slot : Fin 4,
      d.V (AspisR1.childIndex (AspisR1.parentIndex (q j)) slot) =
        V (AspisR1.childIndex (AspisR1.parentIndex (q j)) slot)) :
    QueryResidualBridge.values d q j = QueryResidualBridge.values (withWords d W V) q j := by
  have eq : (fun slot : Fin 4 => d.V (AspisR1.childIndex (AspisR1.parentIndex (q j)) slot)) =
      (fun slot : Fin 4 => V (AspisR1.childIndex (AspisR1.parentIndex (q j)) slot)) := funext same
  unfold QueryResidualBridge.values curveValue SecondFoldRestoration.channels
  change _ = _
  simp only [withWords]
  rw [eq]

theorem closed_sum (iota : K →+* E) (d : MatchingSupport.Data E)
    (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (same : ∀ j : Fin 22, ∀ slot : Fin 4,
      d.V (AspisR1.childIndex (AspisR1.parentIndex (q j)) slot) =
        V (AspisR1.childIndex (AspisR1.parentIndex (q j)) slot)) :
    HchecksAccumulator.ClosedSum iota d q rho ↔
      HchecksAccumulator.ClosedSum iota (withWords d W V) q rho := by
  have values : QueryResidualBridge.values d q = QueryResidualBridge.values (withWords d W V) q :=
    funext (fun j => second_value d W V q j (same j))
  unfold HchecksAccumulator.ClosedSum
  rw [values]
  rfl

/-- Pairing checks do not depend on either full word. -/
theorem pairing (d : MatchingSupport.Data E) (W : Fin 29 → InitialWord E) (V : FinalWord E) :
    MatchingSupport.AcceptedPairing d ↔ MatchingSupport.AcceptedPairing (withWords d W V) := Iff.rfl

/-- The R3 terminal expression uses the parsed Y values, not the words. -/
theorem semantic_terminal (pub : R0P.Public SemanticPublicWire.M31)
    (v : LiteralOpeningView.View) (d : MatchingSupport.Data LiteralTranscript.E)
    (W : Fin 29 → InitialWord LiteralTranscript.E) (V : FinalWord LiteralTranscript.E) :
    R3SemanticRemainingJoins.terminal pub v d =
      R3SemanticRemainingJoins.terminal pub v (withWords d W V) := rfl

#print axioms batched_fibre
#print axioms first_fold
#print axioms first_match
#print axioms second_value
#print axioms closed_sum
#print axioms pairing
#print axioms semantic_terminal
end AspisR1.OraclePortSelectedArithmeticC4
end
