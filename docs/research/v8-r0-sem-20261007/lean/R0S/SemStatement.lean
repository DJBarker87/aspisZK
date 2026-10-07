import R0.OpeningDefinitions

/-! Statement-only draft. No instance of SourceDraft, RelationDraft, a
probability law, or a soundness certificate is supplied. Each field left for
the lead is assigned an open-question number in SEM_SPEC.md. -/
set_option autoImplicit false
namespace R0S
open scoped BigOperators
open Polynomial AspisWide.InitialEncoder AspisR0.Opening AspisR0.ListsResponses
open AspisPool.AlgorithmicCircleDecoderV7
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Lambda

abbrev Tuple (K : Type) := Fin 29 → InitialMessage K
abbrev Point10 (K : Type) := Fin 10 → K
abbrev Claims (K : Type) := Fin 3 → Fin 29 → K

inductive Variant | baseline | positiveTransfer deriving DecidableEq

inductive Message (K Root : Type)
  | c1 (root : Root)
  | c2 (root : Root)
  | initial (value : K)
  | sumcheck (round : Fin 10) (sent : Fin 27 → K)
  | claims (values : Claims K)

inductive Phase
  | copyLambda | copyChi | theta | zerocheck (coordinate : Fin 10)
  | helperMu | maskEta | sumcheck (round : Fin 10)
  deriving DecidableEq

/-- All semantic challenges are in K; none is in the wider opening field. -/
structure Challenge (K : Type) where
  phase : Phase
  value : K

abbrev Prefix (K Root : Type) := List (Sum (Message K Root) (Challenge K))

structure Coins (K : Type) where
  lambda : K
  chi : K
  theta : K
  zerocheck : Point10 K
  mu : K
  eta : K
  sumcheck : Point10 K

/-- Information available before the initial claim and eta. -/
structure BeforeEta (K : Type) where
  lambda : K
  chi : K
  theta : K
  zerocheck : Point10 K
  mu : K

def beforeEta {K : Type} (c : Coins K) : BeforeEta K :=
  ⟨c.lambda, c.chi, c.theta, c.zerocheck, c.mu⟩

/-- Prover causality is explicit: C2 sees only lambda/chi; each round sees
only earlier sumcheck answers. Private randomness can be fixed externally.
Root-to-word binding and canonical/base-field C1 values are Q10/Q11. -/
structure Strategy (K Root : Type) where
  c1Root : Root
  c1Words : Fin 26 → InitialWord K
  c2 : K → K → Root × (Fin 3 → InitialWord K)
  initial : BeforeEta K → K
  round : BeforeEta K → K → Fin 10 → List K → (Fin 27 → K)
  claims : BeforeEta K → K → Point10 K → Claims K

def words {K Root : Type} (s : Strategy K Root) (c : Coins K) :
    Fin 29 → InitialWord K := Fin.append s.c1Words (s.c2 c.lambda c.chi).2

def roundMessage {K Root : Type} (s : Strategy K Root) (c : Coins K)
    (i : Fin 10) : Fin 27 → K :=
  s.round (beforeEta c) c.eta i ((List.ofFn c.sumcheck).take i.val)

def claims {K Root : Type} (s : Strategy K Root) (c : Coins K) : Claims K :=
  s.claims (beforeEta c) c.eta c.sumcheck

/-- Literal source coefficient convention: only coefficient 1 is omitted. -/
def roundPolynomial {K : Type} [Field K] (carry : K) (sent : Fin 27 → K) : K[X] :=
  C (sent 0) + C (carry - 2 * sent 0 - ∑ j : Fin 26, sent j.succ) * X +
    ∑ j : Fin 26, monomial (j.val + 2) (sent j.succ)

def carry {K Root : Type} [Field K] (s : Strategy K Root) (c : Coins K) : Nat → K
  | 0 => s.initial (beforeEta c)
  | n+1 => if h : n < 10 then
      (roundPolynomial (carry s c n) (roundMessage s c ⟨n,h⟩)).eval (c.sumcheck ⟨n,h⟩)
    else carry s c n

/-- Big-endian source selector; compare R0.eqWeight's little-endian index. -/
def sourceWeight {K : Type} [Field K] (z : Point10 K) (r : Fin 1024) : K :=
  ∏ i : Fin 10, if r.val / 2^(9-i.val) % 2 = 0 then 1-z i else z i

def sourceMLE {K : Type} [Field K] (a : Fin 1024 → K) (z : Point10 K) : K :=
  ∑ r : Fin 1024, sourceWeight z r * a r

def successor {K : Type} [Field K] (z : Point10 K) : Point10 K := fun i =>
  let c := ∏ j : Fin 10, if i.val < j.val then z j else 1
  z i + c - 2*z i*c

def xor12 {K : Type} [Field K] (z : Point10 K) : Point10 K := fun i =>
  if i.val = 6 ∨ i.val = 7 then 1-z i else z i

def sourcePoints {K : Type} [Field K] (z : Point10 K) : Fin 3 → Point10 K := fun j =>
  if j.val = 0 then z else if j.val = 1 then successor z else xor12 z

/-- A candidate adapter, not selected by the draft: Q4 must settle basis and
coordinate transport together. This definition asserts no compatibility. -/
def reversedSourcePoints {K : Type} [Field K] (z : Point10 K) : Fin 3 → Point10 K :=
  fun j i => sourcePoints z j i.rev

def equality {K : Type} [Field K] (a b : Point10 K) : K :=
  ∏ i : Fin 10, (1-a i-b i+2*a i*b i)

def positiveResidual {K : Type} [Field K] (v : Claims K) : K :=
  v 0 1 * v 1 1 * v 0 3 - 1

/-- Q1-Q6: exact source operations to freeze, not assumed soundness facts.
The 94 scalar residuals include selector-weighted sums at their literal
source slots; poseidon has four packed lanes, copy is lane 28. -/
structure SourceDraft (Public K : Type) [Field K] where
  variant : Variant
  publicValid : Public → Prop
  towerBasis : Fin 4 → K
  poseidonAt : Public → Claims K → Point10 K → Fin 4 → K
  scalarAt : Public → Claims K → Point10 K → Fin 94 → K
  copyAt : Public → Claims K → Point10 K → K → K → K
  activeAt : Public → Point10 K → K
  maskAt : Claims K → Point10 K → K
  openingPoints : Point10 K → Fin 3 → Point10 K
  inactive : Finset (Fin 1024)

def packedSemantic {Public K : Type} [Field K] (d : SourceDraft Public K)
    (x : Public) (v : Claims K) (z : Point10 K) (g : Fin 24) : K :=
  ∑ b : Fin 4, d.towerBasis b *
    (if h : 4*g.val+b.val < 94 then d.scalarAt x v z ⟨4*g.val+b.val,h⟩
     else if 4*g.val+b.val = 94 ∧ d.variant = .positiveTransfer then
       sourceWeight z 1014 * positiveResidual v else 0)

def composition {Public K : Type} [Field K] (d : SourceDraft Public K)
    (x : Public) (v : Claims K) (c : Coins K) : K :=
  (∑ i : Fin 4, c.theta^i.val * d.poseidonAt x v c.sumcheck i) +
  (∑ g : Fin 24, c.theta^(g.val+4) * packedSemantic d x v c.sumcheck g) +
  c.theta^28 * d.copyAt x v c.sumcheck c.lambda c.chi

def terminal {Public K : Type} [Field K] (d : SourceDraft Public K)
    (x : Public) (v : Claims K) (c : Coins K) : K :=
  d.maskAt v c.sumcheck + c.eta *
    (equality c.zerocheck c.sumcheck * composition d x v c +
      c.mu * v 0 26 + c.mu^2 * (1-d.activeAt x c.sumcheck) * v 0 26)

def Accepts {Public K Root : Type} [Field K] (d : SourceDraft Public K)
    (x : Public) (s : Strategy K Root) (c : Coins K) : Prop :=
  d.publicValid x ∧ c.eta ≠ 0 ∧ terminal d x (claims s c) c = carry s c 10

/-- Q2-Q5: the unresolved concrete algebraic catalogue and witness decoder.
No value of this record is supplied, and no implication to a payment witness
is assumed. Such an implication is itself a target below. -/
structure RelationDraft (Public Witness K : Type) [Field K] where
  physical : Tuple K → Tuple K
  enabledLink : Public → Fin 136 → Prop
  producer : Public → Tuple K → Fin 136 → (Fin 17 → K)
  consumer : Public → Tuple K → Fin 136 → (Fin 17 → K)
  publicMatches : Public → Tuple K → Prop
  witnessValid : Public → Witness → Prop
  realizes : Tuple K → Witness → Prop
  decode : Public → Tuple K → Option Witness

def rowClaims {Public Witness K : Type} [Field K]
    (r : RelationDraft Public Witness K) (t : Tuple K) (row : Fin 1024) : Claims K :=
  let z : Point10 K := fun b => if row.val / 2^(9-b.val) % 2 = 0 then 0 else 1
  fun j l => sourceMLE (r.physical t l) (sourcePoints z j)

def TupleBaseTyped {Public Witness K : Type} [Field K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    (r : RelationDraft Public Witness K) (t : Tuple K) : Prop :=
  ∀ l : Fin 26, ∀ row : Fin 1024, ∃ a : ZMod AspisCircleGroupOrder.P,
    r.physical t (l.castAdd 3) row = algebraMap (ZMod AspisCircleGroupOrder.P) K a

/-- Exact *form* of the requested constraints, pending the named source
catalogue. No honest masking or already-valid witness is required here. -/
def Algebraic {Public Witness K : Type} [Field K]
    (d : SourceDraft Public K) (r : RelationDraft Public Witness K)
    (x : Public) (t : Tuple K) : Prop :=
  r.publicMatches x t ∧
  (∀ row : Fin 1024, ∀ i : Fin 4,
    d.poseidonAt x (rowClaims r t row)
      (fun b => if row.val / 2^(9-b.val) % 2 = 0 then 0 else 1) i = 0) ∧
  (∀ row : Fin 1024, ∀ i : Fin 94,
    d.scalarAt x (rowClaims r t row)
      (fun b => if row.val / 2^(9-b.val) % 2 = 0 then 0 else 1) i = 0) ∧
  (∀ l, r.enabledLink x l → r.producer x t l = r.consumer x t l) ∧
  (d.variant = .positiveTransfer →
    r.physical t 1 1014 * r.physical t 1 1015 * r.physical t 3 1014 = 1)

def RelationExtractionTarget {Public Witness K : Type} [Field K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    (d : SourceDraft Public K) (r : RelationDraft Public Witness K) : Prop :=
  ∀ x t, TupleBaseTyped r t → Algebraic d r x t → ∃ w,
    r.decode x t = some w ∧ r.witnessValid x w ∧ r.realizes t w

def liftTuple {K E : Type} [Field K] [Field E] (ι : K →+* E) (t : Tuple K) : Tuple E :=
  fun l j => ι (t l j)

def ValidExtension {Public Witness K E : Type} [Field K] [Field E]
    (r : RelationDraft Public Witness K) (ι : K →+* E) (x : Public) (t : Tuple E) : Prop :=
  ∃ u w, liftTuple ι u = t ∧ r.witnessValid x w ∧ r.realizes u w

structure Output (K : Type) where
  points : Fin 3 → Point10 K
  pointClaims : Claims K
  inactive : Finset (Fin 1024)

def output {Public K Root : Type} [Field K] (d : SourceDraft Public K)
    (s : Strategy K Root) (c : Coins K) : Output K :=
  ⟨d.openingPoints c.sumcheck, claims s c, d.inactive⟩

/-- Semantic output is only part of Data. z0/z1/y arrive in step 3 (Q12). -/
def toOpeningData {K E : Type} [Field K] [Field E] (ι : K →+* E)
    (W : Fin 29 → InitialWord E) (o : Output K)
    (z0 z1 : AspisR0.ChordGeometry.Point E) (y : Fin 29 → Fin 2 → E) : Data E :=
  ⟨W,z0,z1,y,fun j b => ι (o.points j b),fun j l => ι (o.pointClaims j l),o.inactive⟩

def AllClaims {K E : Type} [Field K] [Field E] (ι : K →+* E)
    (o : Output K) (t : Tuple E) : Prop :=
  ∀ j l, ι (o.pointClaims j l) =
    AspisR0.RoundNormalization.dot (eqWeight (fun b => ι (o.points j b))) (t l)

/-- Q7: distribution over a finite abstract randomness space. None is an
abort and never accepts; successful coins are not renormalized. -/
structure Experiment (Ω K : Type) where
  weight : Ω → ℚ
  coins : Ω → Option (Coins K)

def Probability {Ω K : Type} [Fintype Ω] (e : Experiment Ω K) (event : Coins K → Prop) : ℚ :=
  ∑ ω, e.weight ω * (match e.coins ω with | none => 0 | some c => if event c then 1 else 0)

def ProbabilityLaw {Ω K : Type} [Fintype Ω] (e : Experiment Ω K) : Prop :=
  (∀ ω, 0 ≤ e.weight ω) ∧ (∑ ω, e.weight ω) = 1

variable {Public Witness K E Root Ω : Type} [Field K] [Field E]
  [Fintype E] [DecidableEq E] [Algebra (ZMod AspisCircleGroupOrder.P) E]

def openingWords (ι : K →+* E) (s : Strategy K Root) (c : Coins K) :
    Fin 29 → InitialWord E := fun l j => ι (words s c l j)

def NoWitness (r : RelationDraft Public Witness K) (ι : K →+* E)
    (x : Public) (s : Strategy K Root) (c : Coins K) : Prop :=
  ∀ t ∈ Lambda (openingWords ι s c), ¬ ValidExtension r ι x t

def AcceptsExact (d : SourceDraft Public K) (ι : K →+* E)
    (x : Public) (s : Strategy K Root) (c : Coins K) : Prop :=
  Accepts d x s c ∧ ∃ t ∈ Lambda (openingWords ι s c), AllClaims ι (output d s c) t

/-- Recommended Q8 formulation: the no-witness event is inside the full
causal experiment, since C2 and Lambda can depend on lambda and chi. -/
def SEMTarget [Fintype Ω] (εSEM : ℚ) (d : SourceDraft Public K)
    (r : RelationDraft Public Witness K) (ι : K →+* E)
    (x : Public) (s : Strategy K Root) (e : Experiment Ω K) : Prop :=
  Probability e (fun c => NoWitness r ι x s c ∧ AcceptsExact d ι x s c) ≤ εSEM

/-- Literal implication form, with its global no-witness quantifier exposed.
This does not condition on a possibly challenge-dependent C2 commitment. -/
def SEMImplicationTarget [Fintype Ω] (εSEM : ℚ) (d : SourceDraft Public K)
    (r : RelationDraft Public Witness K) (ι : K →+* E)
    (x : Public) (s : Strategy K Root) (e : Experiment Ω K) : Prop :=
  (∀ ω c, e.coins ω = some c → NoWitness r ι x s c) →
    Probability e (AcceptsExact d ι x s) ≤ εSEM

/-- The following bad-event recipes are propositions, not established bounds.
Arguments must be computed from fixed candidates and the actual prefix. -/
def RootBad {K : Type} [Field K] (p : K[X]) (c : K) : Prop :=
  p ≠ 0 ∧ p.eval c = 0

def LambdaBad {K : Type} [Field K] (characteristicWitness : K[X]) (c : K) : Prop :=
  RootBad characteristicWitness c

def ChiBad {K : Type} [Field K] (poles : Finset K) (wronskian : K[X]) (c : K) : Prop :=
  c ∈ poles ∨ RootBad wronskian c

def ThetaBad {K : Type} [Field K] (selectedNonzeroRow : K[X]) (c : K) : Prop :=
  RootBad selectedNonzeroRow c

def ZerocheckCoordinateBad {K : Type} [Field K] (nonzeroSlice : K[X]) (c : K) : Prop :=
  RootBad nonzeroSlice c

def MuBad {K : Type} [Field K] (constraintSum helperSum inactiveSum c : K) : Prop :=
  (constraintSum ≠ 0 ∨ helperSum ≠ 0 ∨ inactiveSum ≠ 0) ∧
    constraintSum + c*helperSum + c^2*inactiveSum = 0

def EtaBad {K : Type} [Field K] (maskSum realSum claimed c : K) : Prop :=
  realSum ≠ 0 ∧ maskSum + c*realSum = claimed

def SumcheckBad {K : Type} [Field K] (sent honest : K[X]) (c : K) : Prop :=
  sent ≠ honest ∧ sent.eval c = honest.eval c

/-- Q9/Q13: each family must be constructed using only this prefix. Lambda
uses the C1 family fixed before lambda/chi; later stages use the
post-C2 width-29 family. -/
abbrev BadFamily (K Root : Type) [Field K] := Prefix K Root → Phase → Finset K[X]

def BadAt {K Root : Type} [Field K] (f : BadFamily K Root)
    (p : Prefix K Root) (i : Phase) (c : K) : Prop :=
  ∃ g ∈ f p i, g ≠ 0 ∧ g.eval c = 0

structure Caps where
  c1List : Nat
  fullList : Nat
  lambdaRoots : Nat
  chiPoleRoots : Nat
  chiCollisionRoots : Nat
  thetaDegree : Nat
  muDegree : Nat
  etaDegree : Nat
  roundDegree : Nat
  reserve : Nat

/-- PROPOSAL for Q13 only: retain the old copy envelope and 30-root reserve;
update theta to 28, mu to 2, and charge eta cancellation once per candidate. -/
def proposedCaps : Caps := ⟨100,100,2928,366,365,28,2,1,27,30⟩

def capAt (b : Caps) : Phase → Nat
  | .copyLambda => b.c1List*b.lambdaRoots
  | .copyChi => b.c1List*(b.chiPoleRoots+b.chiCollisionRoots)
  | .theta => b.fullList*b.thetaDegree
  | .zerocheck _ => b.fullList
  | .helperMu => b.fullList*b.muDegree
  | .maskEta => b.fullList*b.etaDegree
  | .sumcheck _ => b.fullList*b.roundDegree

def numerator (b : Caps) : Nat :=
  b.c1List*(b.lambdaRoots+b.chiPoleRoots+b.chiCollisionRoots) +
  b.fullList*(b.thetaDegree+10+b.muDegree+b.etaDegree+10*b.roundDegree) + b.reserve

def epsilonSEM (b : Caps) : ℚ :=
  (numerator b : ℚ) / ((AspisCircleGroupOrder.P^4 : ℚ)-1)

def proposedEpsilonSEM : ℚ := epsilonSEM proposedCaps

def epsilonRound (b : Caps) (i : Phase) : ℚ :=
  (capAt b i : ℚ) / ((AspisCircleGroupOrder.P^4 : ℚ)-1)

/-- Q7: successful conditional atom masses, with missing mass kept as abort. -/
structure Kernel (K Root : Type) where
  mass : Prefix K Root → Phase → K → ℚ
  abort : Prefix K Root → Phase → ℚ

def KernelLaw {K Root : Type} [Field K] [Fintype K] (k : Kernel K Root) : Prop :=
  ∀ p i, (∀ c, 0 ≤ k.mass p i c) ∧ 0 ≤ k.abort p i ∧
    (∑ c, k.mass p i c) + k.abort p i = 1 ∧
    (∀ c, k.mass p i c ≤ 1 / ((Fintype.card K : ℚ)-1)) ∧
    (i = .maskEta → k.mass p i 0 = 0)

/-- Statement of D2 at each legal prefix; neither root families nor their
density are supplied. Prefix legality and law coupling are Q7/Q10/Q13. -/
def D2Target {K Root : Type} [Field K] [Fintype K]
    (legal : Prefix K Root → Phase → Prop) (k : Kernel K Root)
    (f : BadFamily K Root) (b : Caps) : Prop :=
  ∀ p i, legal p i →
    (∑ c, k.mass p i c * (if BadAt f p i c then 1 else 0)) ≤ epsilonRound b i

def CoverageTarget (d : SourceDraft Public K) (r : RelationDraft Public Witness K)
    (ι : K →+* E) (x : Public) (s : Strategy K Root) (f : BadFamily K Root)
    (history : Coins K → List (Prefix K Root × Challenge K)) : Prop :=
  ∀ c, NoWitness r ι x s c ∧ AcceptsExact d ι x s c →
    ∃ pc ∈ history c, BadAt f pc.1 pc.2.phase pc.2.value

/-- Q11: no canonicality/subfield hypothesis is hidden in Strategy. -/
def C1BaseTyped [Algebra (ZMod AspisCircleGroupOrder.P) K] (s : Strategy K Root) : Prop :=
  ∀ l j, ∃ a : ZMod AspisCircleGroupOrder.P,
    s.c1Words l j = algebraMap (ZMod AspisCircleGroupOrder.P) K a

#print axioms roundPolynomial
#print axioms terminal
#print axioms Algebraic
#print axioms RelationExtractionTarget
#print axioms toOpeningData
#print axioms SEMTarget
#print axioms SEMImplicationTarget
#print axioms D2Target
#print axioms CoverageTarget
#print axioms proposedEpsilonSEM
end
end R0S
