import R1CandidateDescent
import R1RawOpening
import R1D18OpeningWeights

/-! Instantiate the seven-row opening algebra with the D18 point weights and
recover the typed candidate/point/extra-claim interface used by the existing
semantic proof. Circle rows and the extra row remain explicit inputs. This is
an E-valued coefficient model, not a parser, Rust, transcript, or spend theorem. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace AspisR1.SemanticOpening
open scoped BigOperators
open AspisCircleGroupOrder AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

/-- Raw rows in verifier order: inactive, three semantic points, extra,
then the two circle evaluations. -/
def rows (inactive : Finset (Fin 1024)) (points : Fin 3 → Fin 10 → E)
    (extra : Fin 1024 → E) (circle : Fin 2 → Fin 1024 → E) :
    Fin 7 → Fin 1024 → E :=
  ![AspisR0.Opening.coeffWeight rowEquiv (AspisR0.Opening.indicator inactive),
    tensorPoint (points 0), tensorPoint (points 1), tensorPoint (points 2),
    extra, circle 0, circle 1]

theorem rows_point (inactive : Finset (Fin 1024)) (points : Fin 3 → Fin 10 → E)
    (extra : Fin 1024 → E) (circle : Fin 2 → Fin 1024 → E) (j : Fin 3) :
    rows inactive points extra circle ⟨j.val + 1, by omega⟩ = tensorPoint (points j) := by
  fin_cases j <;> rfl

theorem rowMap_id_eq_dot (w m : Fin 1024 → E) :
    AspisR1.RawFunctionalWeights.rowMap (RingHom.id E) w m =
      AspisR0.RoundNormalization.dot w m := by
  change (∑ i, m i * w i) = ∑ i, w i * m i
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- This has the point/extra/codeword-typing conjuncts of the older opening
witness, with the new literal candidate list and the concrete D18 transport. -/
def Witness (S : Fin 29 → Subfield E) (d : AspisR1.MatchingSupport.Data E)
    (points : Fin 3 → Fin 10 → E) (extra : Fin 1024 → E)
    (t : AspisR1.ConcreteBinding.Tuple E) : Prop :=
  t ∈ AspisR1.ConcreteBinding.candidates d.W ∧
  (∀ j : Fin 3, ∀ l : Fin 29,
    d.Y ⟨j.val, by omega⟩ l = AspisR0.RoundNormalization.dot
      (AspisR0.Opening.coeffWeight rowEquiv
        (AspisR0.Opening.eqWeight (reversePoint (points j)))) (t l)) ∧
  (∀ l : Fin 29, d.Y 3 l = AspisR0.RoundNormalization.dot extra (t l)) ∧
  (∀ l i, exactInitialEncoder (t l) i ∈ S l)

theorem claims_imply_witness
    (S : Fin 29 → Subfield E) (d : AspisR1.MatchingSupport.Data E)
    (typed : AspisR1.CandidateDescent.WordTyped S d.W)
    (inactive : Finset (Fin 1024)) (points : Fin 3 → Fin 10 → E)
    (extra : Fin 1024 → E) (circle : Fin 2 → Fin 1024 → E)
    (hclaims : AspisR1.MatchingSupport.Claims
      (AspisR1.RawOpening.withRows (RingHom.id E) (rows inactive points extra circle) d)) :
    ∃ t, Witness S d points extra t := by
  obtain ⟨t, ht, hrows, _⟩ := hclaims
  refine ⟨t, ht, ?_, ?_, AspisR1.CandidateDescent.candidate_codeword_typed
    S d.W typed t ht⟩
  · intro j l
    have h := hrows ⟨j.val, by omega⟩ l
    change AspisR1.RawFunctionalWeights.rowMap (RingHom.id E)
      (rows inactive points extra circle ⟨j.val + 1, by omega⟩) (t l) = _ at h
    rw [rows_point, rowMap_id_eq_dot] at h
    have hweight : tensorPoint (points j) =
        AspisR0.Opening.coeffWeight rowEquiv
          (AspisR0.Opening.eqWeight (reversePoint (points j))) := by
      funext i
      exact (coeffWeight_eq_tensorPoint (points j) i).symm
    rw [hweight] at h
    exact h.symm
  · intro l
    have h := hrows 3 l
    change AspisR1.RawFunctionalWeights.rowMap (RingHom.id E) extra (t l) = _ at h
    rw [rowMap_id_eq_dot] at h
    exact h.symm

theorem large_matching_implies_witness
    (S : Fin 29 → Subfield E) (d : AspisR1.MatchingSupport.Data E)
    (typed : AspisR1.CandidateDescent.WordTyped S d.W)
    (inactive : Finset (Fin 1024)) (points : Fin 3 → Fin 10 → E)
    (extra : Fin 1024 → E) (circle : Fin 2 → Fin 1024 → E)
    (hgood : AspisR1.MatchingSupport.Good
      (AspisR1.RawOpening.withRows (RingHom.id E) (rows inactive points extra circle) d))
    (haccepted : AspisR1.MatchingSupport.AcceptedPairing
      (AspisR1.RawOpening.withRows (RingHom.id E) (rows inactive points extra circle) d))
    (hcard : 9558 ≤ (AspisR1.MatchingSupport.matchingSet
      (AspisR1.RawOpening.withRows (RingHom.id E) (rows inactive points extra circle) d)).card) :
    ∃ t, Witness S d points extra t :=
  claims_imply_witness S d typed inactive points extra circle
    (AspisR1.MatchingSupport.large_matching_implies_claims _ hgood haccepted hcard)

/-- The recovered coefficient tuple has subfield-typed semantic rows. -/
theorem witness_rows_typed
    (S : Fin 29 → Subfield E) (d : AspisR1.MatchingSupport.Data E)
    (points : Fin 3 → Fin 10 → E) (extra : Fin 1024 → E)
    (t : AspisR1.ConcreteBinding.Tuple E) (ht : Witness S d points extra t) :
    ∀ l r, t l (rowEquiv r) ∈ S l := by
  intro l r
  exact AspisWide.SubfieldDescent.initialMessage_subfield_descent
    (S l) (t l) (ht.2.2.2 l) (rowEquiv r)

#print axioms rows_point
#print axioms rowMap_id_eq_dot
#print axioms claims_imply_witness
#print axioms large_matching_implies_witness
#print axioms witness_rows_typed
end AspisR1.SemanticOpening
end
