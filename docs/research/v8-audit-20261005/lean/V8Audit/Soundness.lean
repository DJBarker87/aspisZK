import AspisV8R16.BalancedTransport
import AspisV8R17.TwoChannelImageGate
import AspisV8R19.ChannelFold
import AspisV8R19.R548CompactBoundaryRejoin
import AspisV8R19.R552Merkle8LeafPathBinding

/-!
V8 audit 2026-10-05, Phase 1: top-down soundness skeleton for the frozen profile
`AV8/R102/sparseG-bitperm-two-swaps/quadratic-channel-fold/merkle8-research-v1`.

Open nodes are propositions only.  The six `theorem` lines at the end bind
closed nodes to theorems already in the tree at 4e0f47381; no new lemma is
proved.  The tree has no Lean model of the R102 verifier or of its
Fiat–Shamir experiment, so the experiment is the opaque constant `r102`.
-/
set_option autoImplicit false
namespace V8Audit.Soundness

/-- `p = 2^31 - 1`; the challenge field is `K = F_{p^4}`. -/
def p : ℕ := 2147483647
def K : ℚ := (p : ℚ) ^ 4

/-- Rounds of the R102 interactive protocol that draw fresh verifier coins. -/
inductive Round where
  /-- theta, ten zerocheck coordinates, mu, eta, ten degree-27 semantic rounds
  and the terminal check against the 87 point claims -/
  | semantic
  /-- two sequential distinct circle points, each answered by 29 components -/
  | oodPair
  /-- nonzero gamma batching the 29 committed columns -/
  | gamma
  /-- beta folding the ordinary and sparse-G channels after p0 and p2 -/
  | beta
  /-- tau mixing the chord-image residuals -/
  | tau
  /-- alpha0 for the single four-to-one circle fold producing Final256 -/
  | alpha0
  /-- 22 distinct fibres out of 262144 -/
  | query
  /-- rho batching the 44 per-channel query-consistency residuals -/
  | rho
  /-- kappa and the four degree-six relation rounds with their terminal -/
  | relation

/-- Round-by-round targets at the exact R102 parameters.  `gamma` and `alpha0`
carry the list factor 100; `oodPair` is the two-point collision bound for a
list of 100 tuples of degree at most 1024.  These are the numbers of the
conditional 7 September arithmetic; whether each is a proved bound is the
content of nodes S10–S18. -/
def target : Round → ℚ
  | .semantic => 396430 / (K - 1)
  | .oodPair => (100 ^ 2 * 1024 ^ 2 : ℚ) / ((K - (p : ℚ) ^ 2) * (K - (p : ℚ) ^ 2 - 1))
  | .gamma => 2800 / (K - 1)
  | .beta => 2 / K
  | .tau => 4 / (K - 1)
  | .alpha0 => 300 / K
  | .query => (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ)
  | .rho => 44 / (K - 1)
  | .relation => 24 / K

def targetTotal : ℚ :=
  target .semantic + target .oodPair + target .gamma + target .beta + target .tau +
    target .alpha0 + target .query + target .rho + target .relation

/-- Commitment and compilation loss as a function of the number of oracle
queries, in the shape of the BCS bound for a 208-bit digest.  A target shape:
no theorem in the tree states it for the R102 transcript. -/
def authTarget (queries : ℕ) : ℚ := 3 * ((queries : ℚ) ^ 2 + 1) / 2 ^ 208

/-- The Fiat–Shamir-compiled R102 verifier against a prover with oracle access.
`queries` counts every oracle call, including all three nonce regions; no
error is divided by a work factor. -/
structure VerifierExperiment where
  Adv : Type
  queries : Adv → ℕ
  /-- probability that the verifier accepts and the extractor returns no valid
  payment witness -/
  acceptWithoutWitness : Adv → ℚ
  /-- round-by-round knowledge error of the interactive protocol -/
  roundError : Round → ℚ

instance : Inhabited VerifierExperiment :=
  ⟨{ Adv := Unit, queries := fun _ => 0, acceptWithoutWitness := fun _ => 0,
     roundError := fun _ => 0 }⟩

opaque r102 : VerifierExperiment

def roundTotal (E : VerifierExperiment) : ℚ :=
  E.roundError .semantic + E.roundError .oodPair + E.roundError .gamma + E.roundError .beta +
    E.roundError .tau + E.roundError .alpha0 + E.roundError .query + E.roundError .rho +
    E.roundError .relation

/-- SOUNDNESS GOAL.  Knowledge soundness of the Fiat–Shamir-compiled R102
verifier at 100 bits with zero grinding credit: every round-by-round error is
at most its explicit target, the targets sum to at most `2^-100`, and every
prover with `Q` oracle queries makes the verifier accept without an extractable
payment witness with probability at most `(Q + 1)·Σ errors + authTarget Q`. -/
def SoundnessGoal : Prop :=
  (∀ r, r102.roundError r ≤ target r) ∧
  targetTotal ≤ 1 / 2 ^ 100 ∧
  ∀ A, r102.acceptWithoutWitness A ≤
    ((r102.queries A : ℚ) + 1) * roundTotal r102 + authTarget (r102.queries A)

/-- Named propositions about R102 objects with no Lean model in the tree.
None is asserted; the docstring of the node using a field is its statement. -/
structure Claims where
  verifierRefinement : Prop
  preGammaTupleList : Prop
  preBetaQuotientPair : Prop
  farFinalBounded : Prop
  paymentWitnessExtraction : Prop
  listCapAtExactParameters : Prop

instance : Inhabited Claims := ⟨⟨True, True, True, True, True, True⟩⟩
opaque r102Claims : Claims

/-! ## Composition, compilation and arithmetic -/

/-- S02 (DEFERRED, refinement). The Rust/SBF verifier of source manifest
26755a42… accepts exactly the proofs the model verifier accepts and draws the
same challenges from the same transcript.  Not decomposed. -/
def Node_S02 : Prop := r102Claims.verifierRefinement

/-- S03. Fiat–Shamir compilation for the R102 transcript in the random-oracle
model: acceptance without an extractable witness is at most
`(Q + 1)·Σ round errors + authTarget Q`, with adaptive queries, cache hits,
sampler rejection and the three prover-chosen nonces all inside `Q`. -/
def Node_S03 : Prop :=
  ∀ A, r102.acceptWithoutWitness A ≤
    ((r102.queries A : ℚ) + 1) * roundTotal r102 + authTarget (r102.queries A)

/-- S04 (arithmetic). The nine targets sum to at most `2^-100`.  Exact rational
evaluation outside Lean gives `2^-104.2615`. -/
def Node_S04 : Prop := targetTotal ≤ 1 / 2 ^ 100

/-! ## One node per round -/

/-- S10. Semantic rounds: a false masked claim survives the ten degree-27
rounds, the helper, zerocheck, copy and point-lane checks with probability at
most `396430 / (p^4 - 1)`, the V7 fixed-family inventory. -/
def Node_S10 : Prop := r102.roundError .semantic ≤ target .semantic

/-- S11. OOD pair: two distinct tuples of a pre-committed list of at most 100
agree on both 29-component OOD vectors with probability at most the two-point
collision bound. -/
def Node_S11 : Prop := r102.roundError .oodPair ≤ target .oodPair

/-- S12. Gamma: if the committed 29-column word is not explained on more than
38229 symbols by a listed tuple with the claimed OOD values, the gamma-batched
quotient is close to the code with probability at most `2800 / (p^4 - 1)`. -/
def Node_S12 : Prop := r102.roundError .gamma ≤ target .gamma

/-- S13. Beta: if the pre-beta quotient pair does not satisfy both channel
claims, the folded claim `p0 + beta p1 + beta² p2` holds for at most two beta. -/
def Node_S13 : Prop := r102.roundError .beta ≤ target .beta

/-- S14. Tau: a nonzero vector of chord-image residuals passes the combined
image check for at most four tau. -/
def Node_S14 : Prop := r102.roundError .tau ≤ target .tau

/-- S15. Alpha0: if the virtual quotient word is far from the degree-1023
code, its four-to-one fold is within the final list radius of a degree-255
polynomial with probability at most `300 / p^4`. -/
def Node_S15 : Prop := r102.roundError .alpha0 ≤ target .alpha0

/-- S16. Query: if Final256 disagrees with the fold of the committed word on
all but at most 9557 fibres, 22 uniform distinct fibres all miss the
disagreement with probability `C(9557,22) / C(262144,22)`. -/
def Node_S16 : Prop := r102.roundError .query ≤ target .query

/-- S17. Rho: 44 per-channel query residuals fixed before rho, not all zero,
cancel in the batched check for at most 44 rho. -/
def Node_S17 : Prop := r102.roundError .rho ≤ target .rho

/-- S18. Relation: a false ordinary claim survives kappa and the four
degree-six relation rounds with probability at most `24 / p^4`. -/
def Node_S18 : Prop := r102.roundError .relation ≤ target .relation

/-- S01 (composition). The nine round bounds, the arithmetic and the
compilation theorem are, by definition, the soundness goal. -/
def Node_S01 : Prop :=
  Node_S10 → Node_S11 → Node_S12 → Node_S13 → Node_S14 → Node_S15 → Node_S16 → Node_S17 →
    Node_S18 → Node_S04 → Node_S03 → SoundnessGoal

/-! ## Extraction claims the round nodes rest on -/

/-- S20. Before gamma is drawn, the committed C1 and C2 words and the two OOD
vectors determine a list of at most 100 codeword tuples such that every
accepting continuation is explained by a member of the list, including
branches where a partial provider returns none (the good-anchor/same-final and
no-close-anchor classes of the 7 September decision). -/
def Node_S20 : Prop := r102Claims.preGammaTupleList

/-- S21. Before beta is drawn, the ordinary and sparse-G quotient words and
their weights are fixed, so that the pair, not only its beta-combination, is
extractable; list multiplicity and gamma dependence enter the bound. -/
def Node_S21 : Prop := r102Claims.preBetaQuotientPair

/-- S22. Accepted executions whose Final256 is not the fold of any listed
candidate (far-final accepted extraction) have total probability bounded by
the alpha0 and query targets. -/
def Node_S22 : Prop := r102Claims.farFinalBounded

/-- S23. An accepted execution whose extracted coefficients satisfy every
linear check yields a valid payment witness, except on semantic-challenge
events of stated probability (including a zero compact-round challenge). -/
def Node_S23 : Prop := r102Claims.paymentWitnessExtraction

/-- S24. At agreement above 38229 of `2^20` symbols the initial code, and above
9557 of `2^18` the final code, have at most 100 and 99 codewords in any ball;
the V7 theorems apply to the R102 code because the basis transport does not
change the codebook (S31). -/
def Node_S24 : Prop := r102Claims.listCapAtExactParameters

/-- S12c (composition). S20 with S24 and S11 reduce the gamma round to a root
count of a fixed nonzero degree-28 polynomial per listed tuple. -/
def Node_S12c : Prop := Node_S20 → Node_S24 → Node_S11 → Node_S12

/-- S13c (composition). S21 with the quadratic identity S32 gives S13. -/
def Node_S13c : Prop := Node_S21 → Node_S13

/-- S15c (composition). S20, S21, S22 and S24 give the alpha0 and query rounds
S15 and S16. -/
def Node_S15c : Prop := Node_S20 → Node_S21 → Node_S22 → Node_S24 → Node_S15 ∧ Node_S16

/-! ## Closed nodes: existing theorems -/

/-- S30. Eight-way depth-six commitment binding: two authenticated openings of
one root at the same slots either agree on packed values and salt or exhibit a
collision in the full hash trace. -/
def Node_S30 : Prop := type_of% @AspisV8R19.R552.depth6_leaf_path_binding
theorem node_S30 : Node_S30 := @AspisV8R19.R552.depth6_leaf_path_binding

/-- S31. The basis transport is injective with explicit inverse on all of
`F^I`, so `range (E ∘ T) = range E`: distance and list bounds of the code are
unchanged by the R16 repair and by the two-swap order. -/
def Node_S31 : Prop := type_of% @AspisV8R16.inverse_transport.{0, 0}
theorem node_S31 : Node_S31 := @AspisV8R16.inverse_transport.{0, 0}

/-- S32. Channel-fold identity: `Σ lerp(qR,qG,β)·lerp(wR,wG,β)` is the
quadratic `P0 + β·(P1 + β·P2)` in beta with coefficients fixed by the pair. -/
def Node_S32 : Prop := type_of% @AspisR19.ChannelFold.quadratic_dot_product.{0, 0}
theorem node_S32 : Node_S32 := @AspisR19.ChannelFold.quadratic_dot_product.{0, 0}

/-- S33. A nonzero vector of four image residuals is annihilated by at most
three image challenges. -/
def Node_S33 : Prop := type_of% @AspisV8R17.badImageChallenges_card.{0}
theorem node_S33 : Node_S33 := @AspisV8R17.badImageChallenges_card.{0}

/-- S34. A nonzero vector of `n + 1` residuals is annihilated by at most `n`
batching challenges. -/
def Node_S34 : Prop := type_of% @AspisV8R17.badCombinedChallenges_card.{0}
theorem node_S34 : Node_S34 := @AspisV8R17.badCombinedChallenges_card.{0}

/-- S35. Compact-round rejoin: with the linear coefficient reconstructed from
a false carried claim, the reconstructed and true degree-27 round polynomials
agree at a challenge `x` exactly when `x = 0`. -/
def Node_S35 : Prop := type_of% @AspisV8R19.R548.reconstructed_eval_eq_iff_zero.{0}
theorem node_S35 : Node_S35 := @AspisV8R19.R548.reconstructed_eval_eq_iff_zero.{0}

#print axioms node_S30
#print axioms node_S31
#print axioms node_S32
#print axioms node_S33
#print axioms node_S34
#print axioms node_S35
end V8Audit.Soundness
