import R0FS.V2

/-! Open statement of the missing semantic/step-3 extension.
No R0 semantic implementation exists in the imported interfaces. The operations
below are data parameters, NOT asserted laws. D1/D2/D3 remain unproved Props.
The semantic-message parameter must be instantiated from source, preserving
its adaptive schedule. In particular, this is not an instance of the existing
five-round rb2, and its witness means payment, not merely point compatibility. -/
set_option autoImplicit false
namespace R0C.SemStatement
open FS FS2 AspisR0.Chord AspisR0.ChordGeometry
open AspisV8PairedCommitment AspisWide.InitialEncoder
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.MemoizedProgramLaw
noncomputable section
attribute [local instance] Classical.propDecidable

variable (K E : Type) [Field K] [Field E]

inductive Msg (SM : Type)
  | semantic (m : SM)
  /-- the step-3 claimed values at the three opening points, sent after the
  last sumcheck challenge -/
  | beforeZ0 (y : Fin 3 → Fin 29 → K)
  | beforeZ1 (y0 : Fin 29 → K)
  | opening (m : R0FS.Msg E)

inductive Chal
  | semantic (c : K)
  | circle (z : Point K)
  | opening (c : R0FS.Chal E)

abbrev Prefix (X SM : Type) := FS.Prefix X (Msg K E SM) (Chal K E)

variable {K E} [Fintype K] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Algebra (ZMod AspisCircleGroupOrder.P) E]
  {X SM W Pf I A : Type} {Sfield : Fin 29 → Subfield E}

/-- Missing source definitions, deliberately without proof fields.
`openingView` must validate the two circle challenges, convert K to E, retain
y0, and construct the old opening statement from the semantic transcript.
No such refinement is claimed here. X is the public initial context; committed
words may occur in SM, so later commitments are not moved before lambda/chi. -/
structure SourceData (X SM W : Type) (Sfield : Fin 29 → Subfield E) where
  semanticRounds : Nat
  /-- The second circle row's fixed fallback point (the reference sampler's
  output on a rejected parameter); supplied by the concrete source instance.
  The first row counts hitting it as a bad outcome. -/
  circleFallback1 : Point K
  semanticBad : Prefix K E X SM → SM → K → Prop
  paymentWitness : X → W → Prop
  openingView : Prefix K E X SM →
    Option (FS.Prefix (R0FS.Stmt E Sfield) (R0FS.Msg E) (R0FS.Chal E))
  decision : Prefix K E X SM → Msg K E SM → Bool

/-- A challenge event, not a side condition on the initial statement. -/
def z0Bad (fallback1 z : Point K) : Prop := BaseRational z ∨ z = fallback1

def z1Bad (z0 z1 : Point K) : Prop := BaseRational z1 ∨ z1 = z0

/-- The SEM positions, then z0 and z1, then the existing five opening rows.
The circle rows use the reference's one-block parameter sampler
(`challenge_qm31`, then the rational map of circle.rs:55); a CM31 parameter
yields a fixed non-rational fallback point (`f0` at the first row, `f1 =
circleFallback1` at the second). The first row is bad only on the fibre
of `f1`, the second (for a prefix whose `z0 ≠ f1`) only on the fibre of
`z0`: one parameter each, so each row is bounded by `(1+δ)/P⁴ ≤ 2/P⁴`. -/
def rowBudget (s : SourceData (K := K) X SM W Sfield) (i : Nat) : ℚ :=
  if i < s.semanticRounds then 396430 / ((Fintype.card K : ℚ) - 1)
  else if i = s.semanticRounds then 2 / (AspisCircleGroupOrder.P : ℚ) ^ 4
  else if i = s.semanticRounds + 1 then 2 / (AspisCircleGroupOrder.P : ℚ) ^ 4
  else R0FS.ε E (i - (s.semanticRounds + 2))

/-- The unproved ideal SEM density target at a fixed pre-challenge prefix.
This is an obligation, not a hypothesis installed into a theorem. -/
def SemanticDensity (s : SourceData (K := K) X SM W Sfield) : Prop :=
  ∀ (P : Prefix K E X SM) (m : SM), P.round < s.semanticRounds →
    mean (fun c : K => indicator (s.semanticBad P m c)) ≤
      396430 / ((Fintype.card K : ℚ) - 1)

def roundBad (s : SourceData (K := K) X SM W Sfield)
    (P : Prefix K E X SM) (m : Msg K E SM) (c : Chal K E) : Prop :=
  (∃ sm k, P.round < s.semanticRounds ∧ m = .semantic sm ∧ c = .semantic k ∧
    s.semanticBad P sm k) ∨
  (∃ y z, P.round = s.semanticRounds ∧ m = .beforeZ0 y ∧ c = .circle z ∧
    z0Bad s.circleFallback1 z) ∨
  (∃ y y0 z0 z1, P.round = s.semanticRounds + 1 ∧
    P.rounds.getLast? = some (.beforeZ0 y, .circle z0) ∧
    m = .beforeZ1 y0 ∧ c = .circle z1 ∧ z1Bad z0 z1) ∨
  (∃ Q om oc, s.openingView P = some Q ∧ m = .opening om ∧ c = .opening oc ∧
    P.round = s.semanticRounds + 2 + Q.round ∧ R0FS.roundBad Q.statement Q.rounds om oc)

def hitFrom (s : SourceData (K := K) X SM W Sfield) (x : X)
    (prev : List (Msg K E SM × Chal K E)) : List (Msg K E SM × Chal K E) → Prop
  | [] => False
  | (m,c) :: rest => roundBad s ⟨x,prev⟩ m c ∨ hitFrom s x (prev ++ [(m,c)]) rest

def doomed (s : SourceData (K := K) X SM W Sfield) (P : Prefix K E X SM)
    (_ : Table I A) : Prop :=
  (¬ ∃ w, s.paymentWitness P.statement w) ∧ ¬ hitFrom s P.statement [] P.rounds

def stateRows (s : SourceData (K := K) X SM W Sfield) :
    FS2.RoundByRound' X (Msg K E SM) (Chal K E) I A where
  doomed := doomed s
  ε := rowBudget s

def extract (s : SourceData (K := K) X SM W Sfield) (x : X) (_ : Table I A) : Option W :=
  if h : ∃ w, s.paymentWitness x w then some (Classical.choose h) else none

/-- Sampler and decoder are operations whose source implementation is missing. -/
def protocol (s : SourceData (K := K) X SM W Sfield)
    (msg : Pf → Nat → Msg K E SM)
    (samp : Nat → Prefix K E X SM → Msg K E SM → FS2.Sampler I A (Chal K E))
    (decode : I → Table I A →
      Option (FS2.Sampler I A (Prefix K E X SM × Msg K E SM × Chal K E))) :
    FS2.Protocol X (Msg K E SM) (Chal K E) W Pf I A where
  r := s.semanticRounds + 7
  msg := msg
  samp := samp
  decode := decode
  extract := extract s

variable [DecidableEq I] [Inhabited A] [Fintype A]

/-- Instances of the FIXED interfaces as goals, with no added proof premises. -/
def Obligations (s : SourceData (K := K) X SM W Sfield)
    (msg : Pf → Nat → Msg K E SM)
    (samp : Nat → Prefix K E X SM → Msg K E SM → FS2.Sampler I A (Chal K E))
    (decode : I → Table I A →
      Option (FS2.Sampler I A (Prefix K E X SM × Msg K E SM × Chal K E))) : Prop :=
  let pr := protocol s msg samp decode
  FS2.D1 pr (stateRows s) ∧ FS2.D2 pr (stateRows s) ∧
    FS2.D3 pr (stateRows s) (FS2.verifier pr s.decision)

end
end R0C.SemStatement
