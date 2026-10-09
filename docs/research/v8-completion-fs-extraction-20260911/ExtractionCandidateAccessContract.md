# Candidate production from permitted data: exact frontier

Source audit, 2026-09-12, base `ab4f61feaca096ae3dae66e39d29f6e36bdca0ec`.
This new contract is not a checked theorem or a successful extractor run.
No build, cache change, or edit to the checked batch was performed.

## 1. Keep the full recovered event

The actual definition in `SelectedResidualHighRecovery.lean` is

```text
RecoveredHigh e family gamma kappa tau alpha :=
  ∃ Q, Witness e gamma kappa tau alpha Q
    ∧ HighSupport (e.raw gamma) Q
    ∧ Recovered e.c1 e.c2 family e.data gamma Q.
```

`Witness` includes literal-family membership, the image/ordinary-row gate,
the SAME actual adaptive final equal to `coefficientFoldLayer 256 alpha Q`,
and `HigherCubicRoot`. `HighSupport` gives at least 200808 complete quotient
fibres. `Recovered` gives some `p ∈ family`, at least 38228 own original
symbols of the actual width29 word, the SAME-Q identity
`original (atGamma e.data gamma) Q = ClaimTransport.batch gamma p`, and
`c1Projection p ∈ EarlyC1Family.family e.c1`.

These existential objects are proof payload, not input capabilities of an
extractor. `EarlyC1Family.family` is explicitly `univ.filter qualifies`,
marked noncomputable/irreducible; `family_card_le_100` bounds its mathematical
cardinality but does not enumerate its elements. The selected residual
classifier's separate `family.card ≤ 1` does not enumerate its member either.

## 2. What the implemented access path actually produces

`ExtractionRecordedC1.rs::extract_first_256` reads a genuine fixed C1
recorded-answer prefix, its expected root, and record/byte/lookup limits.
It has no hash function, new-opening request, encoded-word, coefficient,
mask, or witness input. Success materializes:

```text
256 leaves + 255 subtree parents + 10 ancestors = 521 recorded-node lookups
10 frontier digests
256*(403+32) + 10*26 = 111620 leaf/salt/frontier bytes
256 explicit u32 indices = 1024 further bytes
```

Index construction scans the entire bounded prefix, not just 521 entries.
For the minimal 521-record shape, raw input bytes are 125917 and full32-byte
answers occupy 16672 bytes. Missing/forward/malformed/noncanonical records,
inconsistent answers, truncated collisions and budget exhaustion are explicit
failures. No theorem currently derives their absence from `RecoveredHigh`.

`authenticated_c1.rs::authenticate` checks precisely those fibres and returns
1024 evaluations in each of the 16 semantic columns. `Decoder::solve_base`
multiplies by a public inverse of the exact first-window 1024×1024 generator
matrix. `recover_c1` therefore interpolates that window; it is not an
error-correcting or list-decoding algorithm. Its public inverse construction
is cubic work and was deliberately not repeated by the narrow recorded-log
control. Revalidation of the material uses 256 leaf and 530 parent hash
evaluations; the existing control serves all 786 from cached recorded answers.

The strongest honest conditional decoder endpoint is:

```text
the exact required prefix records are present and well ordered,
authentication resolves the SAME C1 root,
the public generator inverse is correct,
all 1024 selected semantic evaluations equal Enc(p) there
  → recover_c1 returns the semantic16 coefficients of p.
```

The last premise is not a consequence of merely having 38228 own symbols
somewhere. It must be derived, not replaced by candidate-inclusion or
decoder-success assumptions.

## 3. Exact obstructions, with their scope

**Missing access.** `RecoveredHigh` contains no query log or prefix lookup
assertion. With an empty log the implemented resolver returns `MissingRoot`
(or `LookupBudget` if that budget is zero), independently of the algebraic
event. This refutes an interface that quantifies over arbitrary logs and
claims success from `RecoveredHigh` alone. It is not a claim that the actual
source execution has an empty authorized log: the missing premise producer
is exactly that source/log coupling and required-record availability.

**Insufficient opening rank.** One q22 body has 88 original evaluations per
column. Its opening-only linear map from 1024 message coefficients has rank
at most 88 and nullity at least 936. For 16 unconstrained semantic columns
the direct-sum nullity is at least 14976. Thus these values alone cannot
uniquely interpolate the table. This statement does not ignore the root by
calling two different words the same authenticated word; it concerns the
linear values only, not a full-transcript collision or a lower bound against
all cryptographic algorithms using the root, claims and final.

**Fixed-window mismatch.** Let W be the first 1024 symbol positions and E_W
the invertible public evaluation matrix. Start with p; replace its received
values on W by `E_W(p+h)` for a nonzero h and keep `Enc(p)` outside W. The
fixed-window decoder returns `p+h`, while p still has at least
`1048576−1024 = 1047552` own symbols. A faithful commitment can authenticate
this modified word. This is an exact failure of support-to-window recovery,
not a full `RecoveredHigh` counterexample: it does not construct the required
literal retained higher factor or a complete accepted selected execution.
No conclusion is obtained by discarding that part of `RecoveredHigh`.

**Gao is not a minority decoder.** `GaoC1Recovery.recover_coefficients`
requires n≥1025 and at most `floor((n−1025)/2)` erroneous sampled symbols.
`EarlyC1SampleGame.accepted_coefficient_failure_bound` specializes to a
uniform private 513-fibre sample (2052 symbols), and uses the stronger
`earlyC1 received = some p` premise. Up to 128 bad sampled fibres imply at
most 512 symbol errors, within the 513-symbol radius. Its missing-radius
sample event is bounded using global bad-fibre count≤16535. A member with
only 38228 own symbols need not satisfy any of those closeness premises.
Moreover, executable `c1_gao.rs::recover_near` currently takes the fully
materialized `query_graph::Extracted`, uses a reproducibility seed rather
than the proved uniform law, and performs a full-word radius check. It is
not an allowed-access minority extractor supplied by the current proof.

Consequently, this audit does not assert either a full source attack or the
impossibility of another extractor. It identifies why these particular
existing programs do not yet have the requested completeness theorem.

## 4. A non-circular finite reconstruction target

There is a candidate-only construction using **disclosed finals**, not p or
the full word. Fix the SAME Execution and its pre-gamma classifier family
with cardinality≤1. Given 29 distinct gamma nodes and four distinct alpha
nodes at each gamma, read the corresponding final256 vectors. Define:

```text
Qhat(gamma) = SelectedMiddleFourAlpha.Generic.reconstruct
                (alphaNodes gamma) (disclosedFinal gamma)
Uhat(gamma) = ComponentRows.original (atGamma e.data gamma) Qhat(gamma)
phat       = Gamma29Reconstruction.reconstructed gammaNodes Uhat
```

The correct proposed theorem is:

```text
family.card ≤ 1;
gammaNodes.card = 29;
each alphaNodes gamma has cardinality 4;
every disclosed node is the SAME e's actual continuation and satisfies
  RecoveredHigh e family at those actual challenges
  → ∃ p ∈ family, phat = p
      ∧ c1Projection phat ∈ EarlyC1Family.family e.c1.
```

This does not assume that phat belongs to the candidate family. The proof
has genuine existing ingredients:

1. `SelectedMiddleUniqueness.high_support_unique` identifies the high Q at
   each gamma across all four histories (via the full/bad support partition).
2. `SelectedMiddleFourAlpha.Generic.reconstruct_folds` recovers that Q from
   the actual finals; `.reconstruct_local` makes access locality explicit.
   Use this generic theorem, not the middle-only wrapper: RecoveredHigh
   does not assert the middle band's upper support bound.
3. The four witnesses' recovered members, and those at every other gamma,
   all equal the same member because the SAME fixed family has size≤1.
   Therefore Uhat has the same member's actual gamma-batch values.
4. `Gamma29Reconstruction.nodal_reconstruction` and the degree28/29-node
   identity identify all components of phat with that member. This is not
   the invalid inference that interpolation of arbitrary adaptive node
   responses automatically has early-family support.

The interpolation algorithms read no p. However the existing Lean
definitions are mathematical Lagrange constructors, not yet a verified
executable implementation of this entire finite-data API. More importantly,
one successful recovered continuation does not supply 116 such nodes.
The collector cannot test `RecoveredHigh` from partial data by executing
its noncomputable family/support definitions. The displayed per-node event
must be justified by a source experiment and accounted failures, not assumed
as an executable acceptance filter. No new conditional interpolation-only
leaf is added here to conceal this missing producer.

## 5. Concrete replay/opening API and resource contract

The smallest useful allowed-access interface is a **bounded replay handle**,
not `getWord`, `getCandidate`, or `open(i)` to an unmodeled provider:

```text
freezeBeforeGamma(actualRun) -> handleGamma
resumeGamma(handleGamma, permittedForkCoins, limits) ->
  Abort | ResourceLimit | SourceFailure | handleAlpha
resumeAlpha(handleAlpha, permittedForkCoins, limits) ->
  Abort | ResourceLimit | SourceFailure | AcceptedRecord
```

The gamma handle must preserve C1, lambda/chi, C2, theta/z/mu, eta, all ten
semantic rounds, claims, semantic check and both OOD answers: the literal
same completed-OOD pre-gamma prefix. Each alpha handle is later and fixes
its gamma, inactive claim, kappa, tau and response0, immediately before
alpha0. Final and all later query/rho/response data remain adaptive. Each
result must retain parser output, immutable prefix identity, actual challenge
label, final vector, acceptance result and the authorized query/answer trace.

In a ROM these functions may not silently overwrite an already answered
query. Challenge framing, prequeries, repeated inputs, variable retry
consumption, prover state/randomness restoration, and table consistency
need an actual permitted-fork implementation. Duplicate gamma/alpha labels
are not new nodes. Failed/rejected/timed-out runs consume the declared
budgets. The collector stops at a fixed attempt budget B, query budget H
and runtime bound T; no success probability or B/H/T value is supplied by
the deterministic interpolation theorems.

Conditional on obtaining the required node matrix, exact sizes are:

* 29 outer nodes, 4 alpha continuations each: 116 successful continuation
  records, not a bound on attempted runs or random-oracle queries.
* 29696 final field elements, or 475136 bytes in the source's four-u32-limb
  encoding. The actual 697-field body occupies 11152 bytes before the
  roots: final coefficients are NOT tightly packed124-bit query leaves.
  This is final data only, not whole proofs, framing, logs or peak memory.
* 2552 q22 query records across those successful continuations; overlap may
  reduce distinct positions but cannot be assumed.
* Dense applications of the precomputed 4×4 and 29×29 interpolation
  matrices take respectively 118784 and 861184 scalar multiply-accumulates
  for all messages (979968 total), excluding matrix construction, actual
  chord/interpolant maps, field-operation expansion and validation work.

An alternative `materializeRecordedOpenings(prefix,root,S,limits)` must
reassemble S only from already authorized recorded preimages; it requests
no new proof transmission. For 513 arbitrary fibres, a simple no-sharing
upper bound is 513 leaves plus 513×18 parent lookups = 9747 lookups, with
additional bounded-prefix indexing. It can feed a corrected near-Gao
access adapter only if the sample/near-radius/public-code interfaces are
proved. It still does not solve minority-family enumeration. Missing
records and forward references remain explicit failures, not zero mass.

## 6. Same-table validation is downstream, not a candidate oracle

`SameC1CheckedTransferFacts.selected_residuals_construct_transfer_and_membership`
takes a candidate and selected RowsVanish, PoseidonChecks, WeightedAliases,
public source comparisons and carry correspondence for that SAME table. It
constructs transfer/afterstate facts, exact selected input note/nullifier,
decoded membership root and canonical direction/index parsing. It neither
produces that candidate nor assumes a valid witness. The next executable
consumer is `recovered_witness.rs::extract_checked`: decode the produced
semantic16 table and run the actual payment/compiler/context/transition
checks, returning any successful checked witness.

The missing collector theorem must bound, over the actual permitted-access
experiment, accepted-and-RecoveredHigh runs for which bounded replay/access
does not yield a candidate passing that actual validator. It must not replace
this event by `earlyC1 = none`, assume candidate inclusion, assume all selected
forks are recovered, or attach a generic Fiat–Shamir multiplier. The explicit
failure categories are source/replay inconsistency, insufficient distinct
nodes, selected-node residual events, access exhaustion, arithmetic/base
conversion failure, semantic-validator rejection and resource exhaustion.
All their probabilities remain unassigned in this contract.
