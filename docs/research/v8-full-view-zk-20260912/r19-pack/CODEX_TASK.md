# R19: reduce actual verifier cost without hiding the security or resource gap

Start from DJBarker87/aspisZK, branch research/v8-r18-sparse-coded-g-20260921,
commit 77fb78727c8b880b7c029828ad93083ff854f7f6. Inspect the remote first. If it
advanced, reconcile the relevant changes rather than resetting someone else's
work. Do not write to production or deploy. Preserve the current R18 reference.
Use a separate research branch for the new channel-fold protocol.

This packet contains executed C++ models, generated fixed-map tables, Rust
integration drafts, a Lean scalar draft and worked mathematics. NONE of its
new Rust/Lean files were compiled in the supplying environment. No new SBF CU
or full-security theorem is claimed. Run the supplied checks before integration.

## Goal and hard distinction

The current primary is 4.78M CU, despite the R18 structural win. Deliver a real
source-valid reduction and push toward the supported 1.4M budget. Do not close
the task on another rank report or a diagnostic execution at 100M. Keep resource,
privacy, soundness and exact-source gates distinct.

Do two tracks, retaining the best artifact from each. The same-profile track
should advance even if the new-profile proof obligation is blocked.

## Track I: exact R18 behavior

### 1. Source-bind and remove the internal duplicate opening computation

Read R18_STRUCTURAL_RESET.md's internal reference audit, the ACTUAL final staged
r17_host_relation.rs, relation_callback.rs and all R37/R38/R43/R18 transforms.
The repository template is not the final staged caller. Locate the internal
opened_values_reference call after successful paired authentication. It is not
the second complete verifier, which the current primary already omits.

Construct a source-level correspondence covering the selected fibre points,
canonical decoders, gamma combination, shared and per-record inversions,
chord poles, same salt/tag/payload hashes, authentication and linear folds.
Use the supplied algebra, not an opaque 'reference_equivalent' premise. Retain
Domain/Canonical/Authentication/Terminal error behavior. Test every malformed
class at every affected position, including the G accessor's reliance on prior
canonical decoding. Tests should exercise valid records not necessarily coming
from honest proofs, invalid denominators and batch-inverse fallback.

Only after establishing that the duplicate adds no acceptance restriction,
exclude it from a distinctly named primary SBF configuration. Keep it in host
and differential tests. Do not drop any primary validation or image check.
Measure both real fixtures and negatives with unchanged proof bytes.

### 2. Share the two query accumulators exactly

Use src/shared_queries.rs as a first pass. The G query covector is rho^22 times
the R query covector. Keep the old 44 powers, old increment bytes and old
transcript. Derive lambda from the last first-channel scale, not an inverse.
Inject after alpha0 and fold only the remaining three challenges. Compare both
old dense states and all intermediate source query states for arbitrary canonical
values. Source error mapping must stay. This does NOT merge A/E/G base weights.

### 3. Specialize range-proved arithmetic and terminal correction

The checked-release manifest is already optimized. Microbenchmark the supplied
canonical-only one-fold M31 multiply and wrapping arithmetic; do not disable
overflow checks globally. Prove input canonicality along actual callers and
keep the full-u64 reducer for four-product accumulators. Compare assembly/SBF,
not host wall time. Try repeated-halving rotations only where useful; existing
single half is already optimized. Keep all previous field edge regressions.

Run tools/check_stage_inventory.py against actual r17_basis_tables.rs before
using the factored T163 tables. Bind the generator's signed-operator identity to
actual SUPPORT/NEXT. src/factored_correction.rs handles ONE tensor correction;
A has two tensors and E has one. Retain the second A tensor—the R18 ledger
already records a bug caused by omitting it. Reuse point-0 high factors and
shared geometry, and benchmark against the current fused sum-products kernel.
Keep all output groups, inactive/pivot contributions and image residuals.

The product count 408 -> 283 is local and does NOT predict the full A/E CU.
Reject a regressing implementation. Borrow existing workspace; no new giant
stack array or bump-allocator churn. Audit semantic flags against the actual
selected source before attempting any baseline toggle.

## Track II: quadratic channel reduction, explicitly new profile

Read design/CHANNEL_FOLD.md fully. Implement the new two-coefficient binary
sumcheck BEFORE the old first arity-four relation round. Its boundary is P(0)+
P(1), not the fourth-root sum. Source-bind the scalar identities first; compile
the supplied lean/ChannelFold.lean leaves and extend to finite dot products.
Do not present those leaves as extraction or random-oracle theorems.

The prover generates p0=<qR,wR> and p2=<qG-qR,wG-wR> with full image weights.
The verifier reconstructs p1 from the original combined claim, absorbs p0,p2,
then samples beta under a new domain. Keep both original interpolant subtractions
in the pre-channel claim. Set the relation claim to P(beta), without subtracting
another interpolant. Preserve all rejection/canonical checks.

Use one quotient with combined raw numerator lerp(all-G,G,beta) and interpolant
lerp(IR,IG,beta). Use one ordinary compact functional with point scales
[(1-beta)kappa,kappa^2,kappa^3], one sparse G with beta*kappa, and the complete
mixed image terms. No division by beta or 1-beta. Keep BOTH roots, every raw
C1/C2 limb, all component OOD rows and the same mask map/T163.

Define a fresh source profile from initialization. Reconcile the suggested
699-field layout with the literal serializer/parser and query schedule. Old
proofs must reject. Generate two genuine source proofs and test invalid witness,
old-profile, canonical, frontier, numerator, image and final corruption cases.
Use an independent dense new-profile verifier as the host oracle. Do not keep
an expensive duplicate in the measured primary merely for testing, but prove
its acceptance equivalence before separating it.

### Security gates that must NOT be assumed

1. Coherent qR/qG and weights must be fixed in the pre-beta source experiment.
   Extracting only q_beta afterward is insufficient. Handle PCS/list/extraction
   and gamma interaction; any multiplicity belongs in the soundness bound.
2. The degree-two local error bound does not prove the actual FS law. Bind
   rejection, cache hits, prequeries, adaptive choices and query budget. Keep
   zero grinding credit and the existing raw-security objective.
3. Add p0,p2 to the legal-mask/full-view matrix with their affine offsets.
   Replace the two Final256 blocks with their beta-combined block, using real
   source prefixes and schedules. Test the actual opposite-witness target,
   not just a rank. Derive the universal image/compatibility proposition and
   exceptional-event law. Fewer serialized fields is not a privacy proof.
4. If the channel coefficients expose a separator, preserve it and quantify
   the source-valid event. Do not add a hiding provider, IID oracle premise,
   or rank assumption to force a positive result.

Measure the complete new primary early, before an extended formalization run.
Keep expensive proof generation off-chain and functional evaluation compact.
The candidate is not a claim that two different functionals equal one shared
functional: the added quadratic proof is essential.

## Evidence/exit criteria

For each attempted source change, retain real cfg/features, source-chain hashes,
ELF, profile, fixture hashes, heap/frame gate, CU and result. Supported-budget
failure must be visible. Compare same-profile proof bytes exactly; mark new-
profile comparisons as such. A checked rejection is not resource exhaustion.
Keep any rejected optimization and its evidence, rather than selecting a lower
failure total. No cap increase or source-pin waiver to obtain a passing label.

Aim for: a completed reduced-CU primary with source-valid controls; the duplicate
cross-check implication; at least one actual SBF-winning arithmetic/contraction
change; and a compiled, source-exercised channel-fold prototype with its precise
privacy/extraction status. Continue independent targets when a gate remains
open, but do not call the resource or security goal complete unless it is.

Final handoff must state what changed, measured CU for both genuine worlds,
which gates remain, and which artifact is the selected best implementation.
Do not report a hypothetical sub-1.4M total from component arithmetic.
