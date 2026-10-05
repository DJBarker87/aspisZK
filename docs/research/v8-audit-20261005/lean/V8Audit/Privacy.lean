import AspisV8Privacy.HybridBudget
import AspisV8R19.R941BalancedSource223Repair

/-!
V8 audit 2026-10-05, Phase 1: top-down privacy skeleton for the frozen profile
`AV8/R102/sparseG-bitperm-two-swaps/quadratic-channel-fold/merkle8-research-v1`.

Statements only.  This file proves nothing: it contains no `theorem`, no
`sorry` and no `axiom`.  Closed nodes live in `PrivacyAlgebra.lean` (P20–P33)
and `PrivacyOracle.lean` (P40–P50).

The tree at 4e0f47381 has no Lean model of the R102 prover, its transcript or
its published view.  The experiment is therefore an opaque constant `r102`;
constructing it from the Rust source is the DEFERRED refinement node P02.
Nodes about objects with no Lean vocabulary in the tree are fields of the
opaque record `r102Claims`: their mathematical content is the docstring, and
the field is only a name that composition nodes can refer to.
-/
set_option autoImplicit false
namespace V8Audit.Privacy
open AspisV8Privacy
open scoped BigOperators

/-! ## Ledger -/

/-- A ledger entry is a numeric target or UNASSIGNED. -/
inductive Target where
  | assigned (bound : ℚ)
  | unassigned

def Target.value : Target → Option ℚ
  | .assigned bound => some bound
  | .unassigned => none

/-- The seven named terms of `PRIVACY_LEDGER.md`. -/
structure Ledger where
  seed : Target
  salt : Target
  commit : Target
  algebraicBad : Target
  fsConflict : Target
  samplerAbort : Target
  source : Target

/-- The total is defined only when every term is assigned. -/
def Ledger.total (L : Ledger) : Option ℚ := do
  let seed ← L.seed.value
  let salt ← L.salt.value
  let commit ← L.commit.value
  let algebraicBad ← L.algebraicBad.value
  let fsConflict ← L.fsConflict.value
  let samplerAbort ← L.samplerAbort.value
  let source ← L.source.value
  pure (seed + salt + commit + algebraicBad + fsConflict + samplerAbort + source)

/-- The ledger at 4e0f47381.  `PRIVACY_LEDGER.md` assigns no number to any
term ("No numerical global privacy bound is assigned"), and no later note does.
All seven terms are UNASSIGNED; `Ledger.total r102Ledger = none`. -/
def r102Ledger : Ledger :=
  { seed := .unassigned, salt := .unassigned, commit := .unassigned,
    algebraicBad := .unassigned, fsConflict := .unassigned,
    samplerAbort := .unassigned, source := .unassigned }

/-- `p = 2^31 - 1`. -/
def p : ℕ := 2147483647

/-- Sum of the four determinant certificates in the tree (P30 819, P31 1355,
P26 1070, P28 14049), each over `p^4`.  This is a component of
`epsilon_algebraic_bad` under product-uniform fixed-root laws, about
`2^-109.9`.  It is not the ledger term: it omits every event with no
certificate and is not transferred to the adaptive law (P13). -/
def algebraicBadCertifiedComponent : ℚ := (819 + 1355 + 1070 + 14049 : ℚ) / (p : ℚ) ^ 4

/-! ## Experiment -/

/-- One session of the honest R102 prover against an adaptive observer who
shares the random oracle.  `View` is the complete published view: both roots,
both frontiers, the 699 fixed fields (initial claim, semantic rounds, point
rows, inactive sum, component OOD vectors, channel coefficients, relation
rounds, Final256), 22 paired opening records with shared salts, every visible
failure, retry and terminal status, and the observer's own oracle answers.

Games: 0 literal source; 1 mathematical model; 2 ideal field-mask tape;
3 ideal salt tape; 4 lazy commitment table; 5 fresh challenges with no
programming conflict; 6 witness-independent abort law. -/
structure Experiment where
  Obs : Type
  Stmt : Type
  Wit : Type
  View : Type
  allowed : Obs → Prop
  valid : Stmt → Wit → Prop
  Coin : Fin 7 → Type
  coinFintype : ∀ i, Fintype (Coin i)
  coinNonempty : ∀ i, Nonempty (Coin i)
  game : ∀ i, Obs → Stmt → Wit → Coin i → View
  SimCoin : Type
  simFintype : Fintype SimCoin
  simNonempty : Nonempty SimCoin
  sim : Obs → Stmt → SimCoin → View

instance (E : Experiment) (i : Fin 7) : Fintype (E.Coin i) := E.coinFintype i
instance (E : Experiment) (i : Fin 7) : Nonempty (E.Coin i) := E.coinNonempty i
instance (E : Experiment) : Fintype E.SimCoin := E.simFintype
instance (E : Experiment) : Nonempty E.SimCoin := E.simNonempty

instance : Inhabited Experiment :=
  ⟨{ Obs := Unit, Stmt := Unit, Wit := Unit, View := Unit,
     allowed := fun _ => True, valid := fun _ _ => True,
     Coin := fun _ => Unit, coinFintype := fun _ => inferInstance,
     coinNonempty := fun _ => inferInstance, game := fun _ _ _ _ _ => (),
     SimCoin := Unit, simFintype := inferInstance, simNonempty := inferInstance,
     sim := fun _ _ _ => () }⟩

/-- The R102 experiment.  Opaque: no node below can be proved by unfolding. -/
opaque r102 : Experiment

/-- Event distance at most `ε` between games `i` and `j`, for every allowed
observer, every statement and every valid witness. -/
def hop (E : Experiment) (i j : Fin 7) (ε : ℚ) : Prop :=
  ∀ a, E.allowed a → ∀ x w, E.valid x w →
    EventDistanceBound (E.game i a x w) (E.game j a x w) ε

/-- A hop is within a ledger entry only if that entry is assigned. -/
def hopWithin (E : Experiment) (i j : Fin 7) (t : Target) : Prop :=
  ∃ ε, t.value = some ε ∧ hop E i j ε

/-- Full-view zero knowledge at ledger `L`: the source view is within the
ledger total of a simulator that receives the statement and no witness. -/
def PrivacyGoalAt (E : Experiment) (L : Ledger) : Prop :=
  ∃ ε, L.total = some ε ∧
    ∀ a, E.allowed a → ∀ x w, E.valid x w →
      EventDistanceBound (E.game 0 a x w) (E.sim a x) ε

/-- PRIVACY GOAL.  For every public statement and every valid witness (hence
every pair of valid witnesses), the complete published R102 view under the
shared random oracle is within `epsilon_total` of a statement-only simulator,
where `epsilon_total` is the sum of the seven ledger terms.  With the ledger at
4e0f47381 the total is undefined, so this proposition cannot hold until every
term is assigned a number. -/
def PrivacyGoal : Prop := PrivacyGoalAt r102 r102Ledger

/-! ## Vocabulary for the last hop (Question A) -/

/-- The ordinary-channel residual of a same-public witness pair at an accepted
prefix: the quotient-coordinate difference that remains after the C1
corrections and before the H1 repair of P27.  `good` is the event that every
determinant certificate (P26, P28, P30, P31) is nonzero at the prefix.  No
construction of `residual` exists in the tree. -/
structure OrdinaryResidual (E : Experiment) where
  Prefix : Type
  good : Prefix → Prop
  alpha : Prefix → AspisV8R15.ExactTowerBase.QM31Exact
  u : Prefix → AspisV8R15.ExactTowerBase.QM31Exact
  v : Prefix → AspisV8R15.ExactTowerBase.QM31Exact
  residual : Prefix → E.Stmt → E.Wit → E.Wit →
    (AspisV8R19.R738JointObservationModel.Index256 → AspisV8R15.ExactTowerBase.QM31Exact)

instance (E : Experiment) : Inhabited (OrdinaryResidual E) :=
  ⟨{ Prefix := Unit, good := fun _ => True, alpha := fun _ => 0, u := fun _ => 0,
     v := fun _ => 0, residual := fun _ _ _ _ _ => 0 }⟩

opaque r102Residual : OrdinaryResidual r102

/-- Named propositions about R102 objects that have no Lean model in the tree.
None is asserted.  The docstring of the node that uses a field is its
statement. -/
structure Claims where
  merkle8CommitTrace : Prop
  honestChallengeFirstRead : Prop
  samplerChronologyLaw : Prop
  abortWitnessIndependent : Prop
  determinantLawTransfer : Prop
  c1JointCoverage : Prop
  ordinaryRepairApplies : Prop
  gPremises : Prop
  gRepairApplies : Prop
  viewPreservingCoupling : Prop
  retryPublicationLaw : Prop

instance : Inhabited Claims := ⟨⟨True, True, True, True, True, True, True, True, True, True, True⟩⟩
opaque r102Claims : Claims

/-! ## Hop nodes, one per ledger term -/

/-- P02 (DEFERRED, refinement). The literal R102 prover, serializer and
publication path produce the same view law as the mathematical model, up to
`epsilon_source`.  Not decomposed. -/
def Node_P02 : Prop := hopWithin r102 0 1 r102Ledger.source

/-- P03. Replacing the two private 32-byte seeds' expansions by an ideal
field-mask tape changes the view by at most `epsilon_seed`, a
random-oracle forbidden-query bound in the observer's query count. -/
def Node_P03 : Prop := hopWithin r102 1 2 r102Ledger.seed

/-- P04. Replacing the derived per-index leaf salts, shared by C1 and C2, by
an ideal salt tape changes the view by at most `epsilon_salt`. -/
def Node_P04 : Prop := hopWithin r102 2 3 r102Ledger.salt

/-- P05. Replacing both eight-way commitments by one lazily sampled table that
exposes only 208-bit digests of opened paths changes the view by at most
`epsilon_commit`. -/
def Node_P05 : Prop := hopWithin r102 3 4 r102Ledger.commit

/-- P06. Replacing every honest Fiat–Shamir challenge by a fresh sample, with
no overwrite of an answer the observer already holds, changes the view by at
most `epsilon_fs_conflict`. -/
def Node_P06 : Prop := hopWithin r102 4 5 r102Ledger.fsConflict

/-- P07. Sampler exhaustion, duplicate OOD, q22 failure, singular denominators
and every other visible abort have a law that does not depend on the witness,
up to `epsilon_sampler_abort`. -/
def Node_P07 : Prop := hopWithin r102 5 6 r102Ledger.samplerAbort

/-- P08. In the idealised game the published view has a law that a
statement-only simulator reproduces up to `epsilon_algebraic_bad`. -/
def Node_P08 : Prop :=
  ∃ ε, r102Ledger.algebraicBad.value = some ε ∧
    ∀ a, r102.allowed a → ∀ x w, r102.valid x w →
      EventDistanceBound (r102.game 6 a x w) (r102.sim a x) ε

/-- P01 (composition). The seven hop bounds give the privacy goal.  This is
six applications of the triangle inequality P40; it is not written out because
Phase 1 adds no proofs. -/
def Node_P01 : Prop :=
  Node_P02 → Node_P03 → Node_P04 → Node_P05 → Node_P06 → Node_P07 → Node_P08 → PrivacyGoal

/-! ## Inside the commitment, Fiat–Shamir and sampler hops -/

/-- P09. The honest R102 commitment phase (two eight-way trees of depth six,
437-byte and 220-byte leaf inputs, one shared 32-byte salt per index,
interleaved frontiers, 26-byte digest projection) is a forward trace in the
sense of P44, and its bad-coin mass is at most `epsilon_commit`. -/
def Node_P09 : Prop := r102Claims.merkle8CommitTrace

/-- P05c (composition). P44 applied to the trace of P09 gives P05. -/
def Node_P05c : Prop := Node_P09 → Node_P05

/-- P10. Every squeeze and advance address of the honest challenge-generation
segment is unread in the cache that precedes it, except on an event whose mass
is bounded in the observer's query count; verifier replays stay cache hits. -/
def Node_P10 : Prop := r102Claims.honestChallengeFirstRead

/-- P06c (composition). P45, P46 and P47 applied under P10 give P06. -/
def Node_P06c : Prop := Node_P10 → Node_P06

/-- P11. The stage laws P48, P49 and the ordinary and nonzero sampler laws
compose, through the distinct-second circle wrapper and the selected callback
order, into the exact joint law of all R102 challenges and their failures. -/
def Node_P11 : Prop := r102Claims.samplerChronologyLaw

/-- P12. Helper-pole and denominator-zero events, and every other prover-side
abort, occur with probability that differs between any two valid witnesses of
one statement by at most a stated multiple of `1 / p^4`. -/
def Node_P12 : Prop := r102Claims.abortWitnessIndependent

/-- P07c (composition). P50 applied to the law of P11, with P12, gives P07. -/
def Node_P07c : Prop := Node_P11 → Node_P12 → Node_P07

/-! ## Inside the algebraic hop -/

/-- P13. Under the actual adaptive accepted-prefix law, where the 22 query
roots depend on earlier challenges, the probability that some determinant of
P26, P28, P30, P31 vanishes is at most the sum of their fixed-root bounds plus
the first-read losses of P10. -/
def Node_P13 : Prop := r102Claims.determinantLawTransfer

/-- P14. At every accepted prefix and for each of the 16 semantic columns, the
108 base-field observation equations (88 raw openings, three point claims, two
OOD values) have full row rank on that column's legal mask cells, and the 16
solutions can be chosen so that the total initial mask claim is unchanged. -/
def Node_P14 : Prop := r102Claims.c1JointCoverage

/-- P15 (Question A, fold). For every accepted prefix in the good event and
every pair of valid witnesses of one statement, the ordinary residual has zero
first fold: `Σ_s r(d,s) α^s = 0` for all 256 blocks `d`. -/
def Node_P15 : Prop :=
  ∀ (π : r102Residual.Prefix) (x : r102.Stmt) (w w' : r102.Wit),
    r102Residual.good π → r102.valid x w → r102.valid x w' →
      ∀ d : Fin 256,
        AspisR19.R370KernelEvaluation.firstFold 256 (r102Residual.alpha π)
          (r102Residual.residual π x w w') d = 0

/-- P16 (Question A, exact image). Under the same quantifiers the residual is
an exact chord quotient: `r₁₀₂₃ = 0` and `(uv - 1)·r₁₀₂₂ + (u + v)·r₁₀₂₁ = 0`. -/
def Node_P16 : Prop :=
  ∀ (π : r102Residual.Prefix) (x : r102.Stmt) (w w' : r102.Wit),
    r102Residual.good π → r102.valid x w → r102.valid x w' →
      AspisV8R19.R738JointObservationModel.rawFlatten (r102Residual.residual π x w w') 1023 = 0 ∧
      (r102Residual.u π * r102Residual.v π - 1) *
          AspisV8R19.R738JointObservationModel.rawFlatten (r102Residual.residual π x w w') 1022 -
        (-(r102Residual.u π + r102Residual.v π)) *
          AspisV8R19.R738JointObservationModel.rawFlatten (r102Residual.residual π x w w') 1021 = 0

/-- P17 (Question A, inactive balance). Under the same quantifiers the
inverse-transported mask of the residual sums to zero over the 810
copy-inactive rows. -/
def Node_P17 : Prop :=
  ∀ (π : r102Residual.Prefix) (x : r102.Stmt) (w w' : r102.Wit),
    r102Residual.good π → r102.valid x w → r102.valid x w' →
      (∑ n ∈ AspisR19.TwoSwapSourceTable.inactive,
        AspisV8R19.R738JointObservationModel.rawMask ((2 : AspisV8R15.ExactTowerBase.QM31Exact)⁻¹)
          (1 + r102Residual.u π * r102Residual.v π)
          (r102Residual.u π * r102Residual.v π - 1)
          (-(r102Residual.u π + r102Residual.v π))
          (r102Residual.residual π x w w') n) = 0

/-- P18. For every same-public pair on the good event there is an H1 change,
legal on all 809 pad rows, that takes the 214 active rows to the second
witness's helper values and leaves raw openings, point claims, the seven
ordinary relation coefficients and Final256 unchanged. -/
def Node_P18 : Prop := r102Claims.ordinaryRepairApplies

/-- P18c (composition). P27 applied to the residual of P15–P17, on the good
event of P13 and after the C1 step P14, gives P18. -/
def Node_P18c : Prop := Node_P13 → Node_P14 → Node_P15 → Node_P16 → Node_P17 → Node_P18

/-- P19a. For every same-public pair the residual handed to the G step has all
seven plain relation coefficients zero and zero structured moment, and the
271-coordinate semantic-message difference has zero finish-coin moment. -/
def Node_P19a : Prop := r102Claims.gPremises

/-- P19. For every same-public pair on the good event there is a legal G
change that cancels the complete 271-coordinate semantic-message difference
and both channel coefficients while leaving G's openings, points and fold
unchanged. -/
def Node_P19 : Prop := r102Claims.gRepairApplies

/-- P19c (composition). P29 under P19a and the good event of P13 gives P19. -/
def Node_P19c : Prop := Node_P13 → Node_P19a → Node_P19

/-- P1A. The C1, H1 and G corrections compose into a bijection of ideal prover
coins, defined from the view alone, that maps executions of one witness to
executions of the other with the identical complete view; by P41 the two view
laws then coincide on the good event. -/
def Node_P1A : Prop := r102Claims.viewPreservingCoupling

/-- P1B. Failed attempts, retries, the visible attempt count and terminal
failure have a joint law covered by a per-attempt coupling bound and a positive
conditional release bound at every reachable failed history (P42 then
applies). -/
def Node_P1B : Prop := r102Claims.retryPublicationLaw

/-- P08c (composition). The C1, H1 and G repairs, their coupling, the
determinant event and the retry law give the algebraic hop P08. -/
def Node_P08c : Prop :=
  Node_P13 → Node_P14 → Node_P18 → Node_P19 → Node_P1A → Node_P1B → Node_P08

end V8Audit.Privacy
