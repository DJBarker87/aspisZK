import R0.Binding
import R0.Ledger
import R0.QueryLaw
import FS.Theorem
import R0FS.Verifier

/-! # R0 opening layer as an `FS.Protocol` (route A)

The statement fixes everything before step 4 of R0_SOUNDNESS §2 (committed
words, the chord points, the semantic phase's points and claims).  The rounds
are: `values y` → γ, `scalar v` → κ, `unit` → τ, `poly P` → α₀, `final F` → S,
then the final `opening` message.  Messages are the IOP messages themselves,
so the state predicate does not read the table; §6's ledger supplies the bad
sets.  Samplers are abstract functions of fresh answer tuples with an
explicit law (`SamplerLaws`): the tree has no 𝔼-valued sampler law. -/
set_option autoImplicit false
namespace R0FS

open FS AspisR0.Opening AspisR0.ListsResponses AspisR0.Fold AspisR0.Chord
open AspisR0.ChordGeometry AspisR0.RootCounts AspisR0.RoundNormalization
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisWide.InitialEncoder AspisWide.FinalEncoder AspisWide.Agreement
open AspisPool.AlgorithmicCircleDecoderV7 AspisV6Width29CorrelatedAgreement
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open Polynomial
open scoped BigOperators
noncomputable section

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E] {Sfield : Fin 29 → Subfield E}

/-- Fixed before the opening layer.  `z0 ≠ z1`, both non-rational, are the
step-3 challenge conditions (no ledger row; see findings). -/
structure Stmt (E : Type) [Field E] [Algebra (ZMod AspisCircleGroupOrder.P) E]
    (Sfield : Fin 29 → Subfield E) where
  W : Fin 29 → InitialWord E
  /-- lanes are committed in their fields of definition -/
  base : ∀ l i, W l i ∈ Sfield l
  z0 : Point E
  z1 : Point E
  hne : z0 ≠ z1
  h0 : ¬ BaseRational z0
  h1 : ¬ BaseRational z1
  points : Fin 3 → Fin 10 → E
  pointClaims : Fin 3 → Fin 29 → E
  inactive : Finset (Fin 1024)
  transport : Fin 1024 ≃ Fin 1024
  extraWeight : InitialMessage E
  extraClaims : Fin 29 → E
  /-- the semantic phase's acceptance, abstract (premise SEM) -/
  semantic : Prop

inductive Msg (E : Type) [Field E]
  | values (y : Fin 29 → Fin 2 → E)
  | scalar (v : E)
  | unit
  | poly (P : E[X])
  | final (F : FinalMessage E)
  | opening

inductive Chal (E : Type)
  | field (c : E)
  | set (S : Finset (Fin 262144))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod AspisCircleGroupOrder.P) E] in
theorem Chal.field_injective : Function.Injective (Chal.field : E → Chal E) := by
  intro a b h; cases h; rfl

def data (x : Stmt E Sfield) (y : Fin 29 → Fin 2 → E) : Data E :=
  ⟨x.W, x.z0, x.z1, y, x.points, x.pointClaims, x.inactive, x.transport, x.extraWeight, x.extraClaims⟩

/-- Witness: a list candidate matching the point claims, with subfield
descent in the lanes' fields of definition. -/
def Witness (x : Stmt E Sfield) (t : Fin 29 → InitialMessage E) : Prop :=
  t ∈ Lambda x.W ∧ (∀ j l, x.pointClaims j l = dot (coeffWeight x.transport (eqWeight (x.points j))) (t l)) ∧
    (∀ l, x.extraClaims l = dot x.extraWeight (t l)) ∧
    ∀ l i, exactInitialEncoder (t l) i ∈ Sfield l

/-- The extractor (route A): the table is not consulted. -/
def extract {I A : Type} (x : Stmt E Sfield) (_ : Table I A) :
    Option (Fin 29 → InitialMessage E) := by
  classical
  exact if h : ∃ t, Witness x t then some (Classical.choose h) else none

theorem extract_eq_none_iff {I A : Type} (x : Stmt E Sfield)
    (T : Table I A) : extract x T = none ↔ ¬ ∃ t, Witness x t := by
  classical
  unfold extract
  split <;> simp_all

/-! ## Ledger bad sets per round (R0_SOUNDNESS §6) -/

def bad0 (x : Stmt E Sfield) (y : Fin 29 → Fin 2 → E) : Finset E :=
  B1 (virtual (data x y)) ∪ B2 (data x y) ∪ B3 (data x y)
def bad1 (x : Stmt E Sfield) (y : Fin 29 → Fin 2 → E) (γ v : E) : Finset E := B4 (data x y) γ v
def bad2 (x : Stmt E Sfield) (y : Fin 29 → Fin 2 → E) (γ v κ : E) : Finset E := B5 (data x y) γ v κ
def bad3 (x : Stmt E Sfield) (y : Fin 29 → Fin 2 → E) (γ κ τ : E) (P : E[X]) : Finset E :=
  B6 (channels (batch (data x y) γ)) ∪ (if P.natDegree ≤ 6 then B7 (data x y) γ κ τ P else ∅)
/-- Bad query sets: 22-subsets inside a matching set of at most 9557 fibres. -/
def bad4 (x : Stmt E Sfield) (y : Fin 29 → Fin 2 → E) (γ α : E) (F : FinalMessage E)
    (S : Finset (Fin 262144)) : Prop :=
  (matchingFibres (data x y) γ α F).card ≤ 9557 ∧ S.card = 22 ∧
    S ⊆ matchingFibres (data x y) γ α F

/-- The bad condition of one round, given the chronological prefix before it
and the round's message and challenge; `False` off the protocol's shape. -/
def roundBad (x : Stmt E Sfield) (l : List (Msg E × Chal E)) (m : Msg E) (c : Chal E) : Prop :=
  (∃ y γ, l = [] ∧ m = .values y ∧ c = .field γ ∧ γ ∈ bad0 x y) ∨
  (∃ y γ v κ, l = [(.values y, .field γ)] ∧ m = .scalar v ∧ c = .field κ ∧ κ ∈ bad1 x y γ v) ∨
  (∃ y γ v κ τ, l = [(.values y, .field γ), (.scalar v, .field κ)] ∧ m = .unit ∧
    c = .field τ ∧ τ ∈ bad2 x y γ v κ) ∨
  (∃ y γ v κ τ P α, l = [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ)] ∧
    m = .poly P ∧ c = .field α ∧ α ∈ bad3 x y γ κ τ P) ∨
  (∃ y γ v κ τ P α F S, l = [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ),
    (.poly P, .field α)] ∧ m = .final F ∧ c = .set S ∧ bad4 x y γ α F S)

/-- Some round of the list (after the accumulated prefix `prev`) is bad. -/
def goodFrom (x : Stmt E Sfield) (prev : List (Msg E × Chal E)) : List (Msg E × Chal E) → Prop
  | [] => False
  | (m, c) :: rest => roundBad x prev m c ∨ goodFrom x (prev ++ [(m, c)]) rest

/-- A challenge of the prefix fell in its bad set (the prefix is "alive"). -/
def good (x : Stmt E Sfield) (l : List (Msg E × Chal E)) : Prop := goodFrom x [] l

/-- §6 state function: doomed iff no witness is extractable and no challenge
so far fell in its bad set.  The table is ignored (route A). -/
def doomed {I A : Type} (P : Prefix (Stmt E Sfield) (Msg E) (Chal E))
    (_ : Table I A) : Prop :=
  (¬ ∃ t, Witness P.statement t) ∧ ¬ good P.statement P.rounds

/-- The verifier's decision on a complete transcript: R0's `Accept` with the
challenges of the prefix; authentication is trivial in route A (messages are
the words); malformed transcripts are rejected. -/
def decision (P : Prefix (Stmt E Sfield) (Msg E) (Chal E)) (m : Msg E) : Bool := by
  classical
  exact decide (∃ y γ v κ τ Q α F S,
    P.rounds = [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ),
      (.poly Q, .field α), (.final F, .set S)] ∧ m = .opening ∧
    Accept (data P.statement y) γ v κ τ α Q F S P.statement.semantic True)

/-! ## Protocol object -/

/-- Everything the FS layer needs that R0_SOUNDNESS does not fix: block
width and per-round sampler arity, the samplers, the proof encoding, and the
address interface. -/
structure Params (E : Type) [Field E] [Algebra (ZMod AspisCircleGroupOrder.P) E]
    (Sfield : Fin 29 → Subfield E) (Pf I B : Type) (Kw : Nat) where
  k : Nat → Nat
  hk : ∀ i, k i ≤ Kw
  sampler : (i : Nat) → (Fin (k i) → B) → Chal E
  msg : Pf → Nat → Msg E
  addr : Prefix (Stmt E Sfield) (Msg E) (Chal E) → Msg E → I
  decode : I → Table I (Block B Kw) → Option (Prefix (Stmt E Sfield) (Msg E) (Chal E) × Msg E)

variable {Pf I B : Type} {Kw : Nat}

def protocol (p : Params E Sfield Pf I B Kw) :
    Protocol (Stmt E Sfield) (Msg E) (Chal E) (Fin 29 → InitialMessage E) Pf I B Kw where
  r := 5
  msg := p.msg
  k := p.k
  hk := p.hk
  sampler := p.sampler
  addr := p.addr
  decode := p.decode
  extract := fun x T => extract x T

/-- Round errors of §6 (0-based), with `max` giving 105.14 bits at q = 22. -/
def ε (E : Type) [Fintype E] : Nat → ℚ
  | 0 => (336869026605739 + 16800 : ℚ) / ((Fintype.card E : ℚ) - 1)
  | 1 => (400 : ℚ) / (Fintype.card E : ℚ)
  | 2 => (200 : ℚ) / (Fintype.card E : ℚ)
  | 3 => (9396508281246 + 600 : ℚ) / (Fintype.card E : ℚ)
  | 4 => (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ)
  | _ => 0

def roundByRound (_p : Params E Sfield Pf I B Kw) :
    RoundByRound (Stmt E Sfield) (Msg E) (Chal E) I B Kw where
  doomed := fun P T => doomed P T
  ε := ε E

def verifierR0 (p : Params E Sfield Pf I B Kw) (x : Stmt E Sfield) (π : Pf) : Program I (Block B Kw) Bool :=
  verifier (protocol p) decision x π

/-- The sampler laws the ledger assumes: γ nonzero and uniform on 𝔼∖{0},
κ, τ, α₀ uniform on 𝔼, S uniform on 22-subsets of the fibres.  Stated as
upper bounds on point masses.  Not proved here (finding). -/
structure SamplerLaws [Fintype B] (p : Params E Sfield Pf I B Kw) : Prop where
  nonzero : ∀ a, ∃ c, p.sampler 0 a = .field c ∧ c ≠ 0
  gamma : ∀ c : E, mean (fun a : Fin (p.k 0) → B => indicator (p.sampler 0 a = .field c)) ≤
    1 / ((Fintype.card E : ℚ) - 1)
  kappa : ∀ c : E, mean (fun a : Fin (p.k 1) → B => indicator (p.sampler 1 a = .field c)) ≤
    1 / (Fintype.card E : ℚ)
  tau : ∀ c : E, mean (fun a : Fin (p.k 2) → B => indicator (p.sampler 2 a = .field c)) ≤
    1 / (Fintype.card E : ℚ)
  alpha : ∀ c : E, mean (fun a : Fin (p.k 3) → B => indicator (p.sampler 3 a = .field c)) ≤
    1 / (Fintype.card E : ℚ)
  queryCard : ∀ a, ∃ S, p.sampler 4 a = .set S ∧ S.card = 22
  queries : ∀ M : Finset (Fin 262144),
    mean (fun a : Fin (p.k 4) → B =>
      indicator (∃ S, p.sampler 4 a = .set S ∧ S.card = 22 ∧ S ⊆ M)) ≤
    (M.card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ)

end
end R0FS
