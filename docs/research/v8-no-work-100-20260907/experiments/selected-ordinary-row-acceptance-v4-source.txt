import TypedRelationTerminalV3
import SelectedResidualHighRecovery
import SelectedMiddleComponentClaimsV2

/-! Typed ordinary-row acceptance boundary. The causal compact fields construct
the strategy rather than assuming an equality to an unrelated strategy. The
same-Q good gate supplies the entire corrected ordinary-row error vector;
terminal acceptance alone does not. The existing no-good probability is reused
once. No Rust execution, total-word authentication, or challenge law is asserted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedOrdinaryRowAcceptance
open Finset
open AspisV8.CausalCoveredRecovery AspisV8.CausalOrderedRelation
open AspisV8.SelectedReceivedOracle AspisV8.SelectedCoveredRelation
open AspisV8.ReferenceIndependentRelation AspisV8.GammaComponentGame
open AspisV8.SelectedHigherYHighSupport AspisV8.SelectedResidualHighRecovery
open AspisV8.SelectedMiddleComponentClaims
open AspisV8.JointImageGame AspisV8.RelationCompatibleMoment
open AspisV5ComponentCConcreteFoldLinearity
noncomputable section

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev ComponentTuple := Fin 29 → Fin 1024 → K
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

/-- Only the strategy is replaced. The supplied C1/C2 words, OOD data,
weights and claims stay fixed; inactive may depend on gamma. This is not a
constructor from commitment roots or a single parsed Rust execution. -/
def withFields {q : Nat} (e : Execution q)
    (fields : K → K → TypedRelationTerminal.Fields domain q) : Execution q :=
  { e with strategy := fun gamma kappa => (fields gamma kappa).strategy }

def callbackAccepts {q : Nat} (e : Execution q)
    (fields : K → K → TypedRelationTerminal.Fields domain q)
    (gamma kappa tau alpha : K) (queries : OrderedQueryGame.Schedule domain q)
    (rho a1 a2 a3 : K) : Prop :=
  TypedRelationTerminal.sourceAccepts
    (((e.rows gamma).before kappa).snapshot tau
      ((fields gamma kappa).firstResponse tau) alpha)
    ((fields gamma kappa).final tau alpha) (fun j => (queries j : K))
    ((oracle 0 (e.raw gamma)).folded alpha) rho
    ((fields gamma kappa).later tau alpha queries rho) a1 a2 a3

/-- The actual typed scalar terminal event uses the same response0, adaptive
final, ordered query schedule, received values, rho and three later responses. -/
theorem callback_accepts_iff {q : Nat} (e : Execution q)
    (fields : K → K → TypedRelationTerminal.Fields domain q)
    (gamma kappa tau alpha : K) (queries : OrderedQueryGame.Schedule domain q)
    (rho a1 a2 a3 : K) :
    callbackAccepts e fields gamma kappa tau alpha queries rho a1 a2 a3 ↔
      CausalOrderedRelation.accepts (((withFields e fields).rows gamma).before kappa)
        (oracle 0 ((withFields e fields).raw gamma))
        ((withFields e fields).strategy gamma kappa) tau alpha queries rho [a1,a2,a3] :=
  TypedRelationTerminal.source_accepts_iff ((e.rows gamma).before kappa)
    (oracle 0 (e.raw gamma)) (fields gamma kappa) tau alpha queries rho a1 a2 a3

/-- This implication uses the existing full good-anchor gate, not the value
of its cubic error polynomial at one sampled kappa. -/
theorem good_rows_zero {q : Nat} (e : Execution q) (gamma : K)
    (Q : Fin 1024 → K) (good : ¬badAnchor (e.rows gamma) Q) :
    (ComponentRows.rows (atGamma e.data gamma) e.quarter e.weights e.claims
      (e.inactive gamma) Q).errors = 0 := by
  have zero : (replaceRows (e.rows gamma) Q).errors = 0 := by
    by_contra wrong
    exact good (Or.inr (Or.inr wrong))
  rw [← reference_rows]
  exact zero

/-- Exact accepted-event partition. The right branch retains the SAME final
representative and derives its row-zero field. The left branch is not discarded. -/
theorem callback_partition {q : Nat} (e : Execution q)
    (fields : K → K → TypedRelationTerminal.Fields domain q)
    (gamma kappa tau alpha : K) (queries : OrderedQueryGame.Schedule domain q)
    (rho a1 a2 a3 : K) :
    callbackAccepts e fields gamma kappa tau alpha queries rho a1 a2 a3 ↔
      (callbackAccepts e fields gamma kappa tau alpha queries rho a1 a2 a3 ∧
        ¬goodPrefix (withFields e fields) gamma kappa tau alpha) ∨
      (callbackAccepts e fields gamma kappa tau alpha queries rho a1 a2 a3 ∧
        ∃ Q ∈ QuotientFamilySelected.literalFamily (e.raw gamma),
          ¬badAnchor (e.rows gamma) Q ∧
          (fields gamma kappa).final tau alpha = coefficientFoldLayer 256 alpha Q ∧
          (ComponentRows.rows (atGamma e.data gamma) e.quarter e.weights e.claims
            (e.inactive gamma) Q).errors = 0) := by
  classical
  constructor
  · intro accepted
    by_cases good : goodPrefix (withFields e fields) gamma kappa tau alpha
    · obtain ⟨Q, member, anchor, finalEq⟩ := good
      exact Or.inr ⟨accepted, Q, member, anchor, finalEq,
        good_rows_zero e gamma Q anchor⟩
    · exact Or.inl ⟨accepted, good⟩
  · rintro (⟨accepted, _⟩ | ⟨accepted, _⟩) <;> exact accepted

/-- No new row repair: the already fixed component-family root set suffices
once representation and the SAME-Q good gate are known. -/
theorem good_represented_claims {q : Nat} (e : Execution q)
    (Gamma : Finset K) (family : Finset ComponentTuple)
    (gamma : K) (Q : Fin 1024 → K) (p : ComponentTuple)
    (member : p ∈ family) (inside : gamma ∈ Gamma)
    (outside : gamma ∉ familyBad Gamma family e.weights e.claims)
    (represented : (atGamma e.data gamma).original Q = ClaimTransport.batch gamma p)
    (good : ¬badAnchor (e.rows gamma) Q) :
    ExactClaims p e.weights e.claims := by
  exact family_claims_exact Gamma family e.weights e.claims
    (atGamma e.data gamma) e.quarter (e.inactive gamma) Q p member inside outside
    represented (good_rows_zero e gamma Q good)

/-- Direct consumer of the checked residual recovery, with no replacement
quotient or post-gamma component-family choice. The final remains adaptive. -/
theorem recovered_high_claims_exact {q : Nat} (e : Execution q)
    (Gamma : Finset K) (family : Finset ComponentTuple)
    (gamma kappa tau alpha : K) (inside : gamma ∈ Gamma)
    (outside : gamma ∉ familyBad Gamma family e.weights e.claims)
    (recovered : RecoveredHigh e family gamma kappa tau alpha) :
    ∃ Q, Witness e gamma kappa tau alpha Q ∧ HighSupport (e.raw gamma) Q ∧
      ∃ p ∈ family,
        (atGamma e.data gamma).original Q = ClaimTransport.batch gamma p ∧
        ExactClaims p e.weights e.claims := by
  obtain ⟨Q, witness, high, p, member, _own, represented, _early⟩ := recovered
  exact ⟨Q, witness, high, p, member, represented,
    good_represented_claims e Gamma family gamma Q p member inside outside
      represented witness.2.1⟩

/-- The fixed family is quantified before gamma and all later histories.
This is one union over at most one tuple, not 87 separate root charges. -/
theorem fixed_claim_exception_card {q : Nat} (e : Execution q)
    (Gamma : Finset K) (family : Finset ComponentTuple) (one : family.card ≤ 1) :
    (familyBad Gamma family e.weights e.claims).card ≤ 28 :=
  familyBad_card Gamma family one e.weights e.claims

/-- Reuse the existing same-suffix partition and its complete no-good bound.
In particular, no second q/G or 18/A repair is appended on the good branch. -/
theorem repair_once {q : Nat} (e : Execution q) (A G Gamma : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (positive : 0 < q) (count : q ≤ 262144) :
    totalProbability e A G Gamma =
        missingProbability e A G Gamma + goodProbability e A G Gamma ∧
      missingProbability e A G Gamma ≤ CausalCoveredRecovery.ceiling q A G :=
  ⟨probability_partition e A G Gamma,
    missing_bound e A G Gamma ha hg hgamma positive count⟩

#print axioms callback_accepts_iff
#print axioms good_rows_zero
#print axioms callback_partition
#print axioms good_represented_claims
#print axioms recovered_high_claims_exact
#print axioms fixed_claim_exception_card
#print axioms repair_once
end
end AspisV8.SelectedOrdinaryRowAcceptance
