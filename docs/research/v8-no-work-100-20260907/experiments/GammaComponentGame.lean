import ComponentRows
import PreAnchorJoint

/-! Compose one pre-gamma component error with the constructed selected
geometry and actual compact relation grammar. This leaf's recovered-close
interface is deterministic coverage, not an acceptance premise; the selected
near-gamma/source leaf must supply it. All near-final acceptance remains in
the event, including sparse alpha geometry and scalar-only acceptance. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 400000
namespace AspisV8.GammaComponentAux
open AspisV8.ShiftedRowPrefix AspisV8.CausalOrderedRelation
open AspisV8.RepresentedImageGame AspisV8.JointImageGame
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]

/-- Symbolic unit bound: do not unfold the concrete selected domain's
query-schedule sum while unifying a bound on the outer row average. -/
theorem rows_unit {D B : Finset K} {q : Nat} (rows : Rows (K := K))
    (hq : rows.quarter*4=1) (oracle : FixedOracle D B rows.referenceQ)
    (strategy : K → Strategy D q) (support : K → K → K → Prop)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty) (hcount : q≤D.card) :
    supportedRowsProbability rows hq oracle strategy support A G≤1 :=
  avg_le G hg _ _ (fun kappa _ => supported_unit (rows.before kappa) hq oracle
    (strategy kappa) (support kappa) A G ha hg hcount)
end AspisV8.GammaComponentAux

namespace AspisV8.GammaComponentGame
open Finset Polynomial
open AspisV8.OODInterpolant AspisV8.ShiftedRowPrefix
open AspisV8.CausalOrderedRelation AspisV8.SelectedReceivedOracle
open AspisV8.PreAnchorJoint AspisV8.RepresentedImageGame
open AspisV8.ReferenceIndependentRelation AspisV8.JointImageGame
open AspisV8.PartialFoldRecovery AspisV8.ClaimTransport
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

def atGamma (data : Data (K := K)) (gamma : K) : Data (K := K) :=
  { data with gamma := gamma }

def rowPrefix (data : Data (K := K)) (quarter : K) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 3 → Fin 29 → K) (inactive : K → K) (gamma : K) : Rows (K := K) :=
  ComponentRows.rows (atGamma data gamma) quarter w claimed (inactive gamma) 0

def nearProbability {q : Nat} (data : Data (K := K)) (quarter : K) (hq : quarter*4=1)
    (w : Fin 4 → Fin 1024 → K) (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
    (R : K → Fin 1048576 → K) (B : Nat) (strategy : K → K → Strategy domain q)
    (gamma : K) (A G : Finset K) : ℚ :=
  supportedRowsProbability (rowPrefix data quarter w claimed inactive gamma) hq
    (oracle 0 (R gamma)) (strategy gamma) (near (R gamma) B (strategy gamma)) A G

theorem reference_rows (data : Data (K := K)) (quarter : K) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 3 → Fin 29 → K) (inactive : K → K) (gamma : K) (Q : Fin 1024 → K) :
    replaceRows (rowPrefix data quarter w claimed inactive gamma) Q=
      ComponentRows.rows (atGamma data gamma) quarter w claimed (inactive gamma) Q := rfl

/-- Any close image-valid geometric anchor has wrong ordinary rows. This
interface also handles nonexistence of such an anchor by contradiction. -/
theorem near_bound_of_wrong_rows {q : Nat}
    (data : Data (K := K)) (quarter : K) (hq : quarter*4=1)
    (w : Fin 4 → Fin 1024 → K) (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
    (R : K → Fin 1048576 → K) (B : Nat) (strategy : K → K → Strategy domain q)
    (gamma : K)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0<q) (hcount : q≤domain.card) (margin : 5*B+255<262144)
    (wrongRows : ∀ Q : Fin 1024 → K,
      (fibreBad (m := 262144) (exactInitialEncoder Q) (R gamma)).card≤4*B →
      Q 1023=0 → (atGamma data gamma).b*Q 1022-(atGamma data gamma).c*Q 1021=0 →
      (ComponentRows.rows (atGamma data gamma) quarter w claimed (inactive gamma) Q).errors≠0) :
    nearProbability data quarter hq w claimed inactive R B strategy gamma A G≤
      ((q:ℚ)+3)/G.card+24/A.card := by
  let rows := rowPrefix data quarter w claimed inactive gamma
  rcases geometric_joint_dichotomy (R gamma) B A G ha hg margin with
    ⟨_, sparse⟩ | ⟨_, Q, close, _, bound⟩
  · have h := sparse q rows hq (strategy gamma) hcount
    change nearProbability data quarter hq w claimed inactive R B strategy gamma A G≤_
    have hc : (0:ℚ)≤(q+3:ℚ)/G.card := by positivity
    have hd : (3:ℚ)/A.card≤24/A.card := div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)
    exact h.trans (hd.trans (le_add_of_nonneg_left hc))
  · have bad : badReference (replaceRows rows Q) := by
      by_cases h1 : Q 1023=0
      · by_cases h2 : (atGamma data gamma).b*Q 1022-(atGamma data gamma).c*Q 1021=0
        · right; right
          rw [show rows=rowPrefix data quarter w claimed inactive gamma from rfl,reference_rows]
          exact wrongRows Q close h1 h2
        · exact Or.inr (Or.inl h2)
      · exact Or.inl h1
    have h := bound q rows hq (strategy gamma) hpos hcount
    have same : (fun k t a => near (R gamma) B (strategy gamma) k t a ∧
        badReference (replaceRows rows Q))=near (R gamma) B (strategy gamma) := by
      funext k t a
      exact propext (and_iff_left bad)
    rw [same] at h
    exact h

/-- Outside the roots of a fixed component error, ALL close-final acceptance
is bounded. Neither an anchor nor representation of an accepting branch is
assumed; deterministic coverage is supplied for all close image-valid Q. -/
theorem outside_component_roots {q : Nat}
    (data : Data (K := K)) (quarter : K) (hq : quarter*4=1)
    (w : Fin 4 → Fin 1024 → K) (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
    (R : K → Fin 1048576 → K) (B : Nat) (strategy : K → K → Strategy domain q)
    (p : Fin 29 → Fin 1024 → K) (j : Fin 3) (gamma : K)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hpos : 0<q) (hcount : q≤domain.card) (margin : 5*B+255<262144)
    (recoveredClose : ∀ Q : Fin 1024 → K,
      (fibreBad (m := 262144) (exactInitialEncoder Q) (R gamma)).card≤4*B →
      Q 1023=0 → (atGamma data gamma).b*Q 1022-(atGamma data gamma).c*Q 1021=0 →
      ComponentRows.original (atGamma data gamma) Q=batch gamma p)
    (nonzero : (errorPolynomial (covector (w j.succ)) p (claimed j)).eval gamma≠0) :
    nearProbability data quarter hq w claimed inactive R B strategy gamma A G≤
      ((q:ℚ)+3)/G.card+24/A.card := by
  apply near_bound_of_wrong_rows data quarter hq w claimed inactive R B strategy gamma
    A G ha hg hpos hcount margin
  intro Q close h1 h2
  exact ComponentRows.nonzero_component_error_forces_wrong_rows
    (atGamma data gamma) quarter w claimed (inactive gamma) Q p
    (recoveredClose Q close h1 h2) j nonzero

/-- Claims/weights/tuple p are fixed before gamma. The inactive scalar and
entire later causal strategy may depend on gamma. There is no 100-target
union, no positive work credit, and no generic semantic-error inventory. -/
theorem wrong_component_near_bound {q : Nat}
    (data : Data (K := K)) (quarter : K) (hq : quarter*4=1)
    (w : Fin 4 → Fin 1024 → K) (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
    (R : K → Fin 1048576 → K) (B : Nat) (strategy : K → K → Strategy domain q)
    (p : Fin 29 → Fin 1024 → K) (j : Fin 3) (lane : Fin 29)
    (wrong : claimed j lane≠covector (w j.succ) (p lane))
    (A G Gamma : Finset K) (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (hpos : 0<q) (hcount : q≤domain.card) (margin : 5*B+255<262144)
    (recoveredClose : ∀ gamma∈Gamma, ∀ Q : Fin 1024 → K,
      (fibreBad (m := 262144) (exactInitialEncoder Q) (R gamma)).card≤4*B →
      Q 1023=0 → (atGamma data gamma).b*Q 1022-(atGamma data gamma).c*Q 1021=0 →
      ComponentRows.original (atGamma data gamma) Q=batch gamma p) :
    avg Gamma (fun gamma => nearProbability data quarter hq w claimed inactive R B strategy gamma A G)≤
      28/Gamma.card+((q:ℚ)+3)/G.card+24/A.card := by
  have h := avg_polynomial Gamma hgamma
    (errorPolynomial (covector (w j.succ)) p (claimed j))
    (component_error_nonzero (covector (w j.succ)) p (claimed j) lane wrong) 28
    (component_error_degree (covector (w j.succ)) p (claimed j))
    (fun gamma => nearProbability data quarter hq w claimed inactive R B strategy gamma A G)
    (((q:ℚ)+3)/G.card+24/A.card) (by positivity)
    (fun gamma _ => GammaComponentAux.rows_unit
      (rowPrefix data quarter w claimed inactive gamma) hq (oracle 0 (R gamma))
      (strategy gamma) (near (R gamma) B (strategy gamma)) A G ha hg hcount)
    (fun gamma hgamma nonzero => outside_component_roots data quarter hq w claimed inactive
      R B strategy p j gamma A G ha hg hpos hcount margin (recoveredClose gamma hgamma) nonzero)
  convert h using 1 <;> ring

#print axioms reference_rows
#print axioms AspisV8.GammaComponentAux.rows_unit
#print axioms near_bound_of_wrong_rows
#print axioms outside_component_roots
#print axioms wrong_component_near_bound
end
end AspisV8.GammaComponentGame
