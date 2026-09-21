# R17 inspected shared-oracle entrypoint slice

## Entropy adapter and public nonce boundary — 2026-09-21

Base `ca6a52e64e9b8105c10bdfc801c68a276a7d5c19` plus this changeset.
The selected performance_verifier.rs::verify API takes body, binding, public,
transition. Its semantic prefix absorbs the R17 profile, positive-transfer
descriptor, payment-extraction profile, binding, C1 root, lambda/chi and C2
root in order. It has no public mask-nonce/context argument and does not call
begin_state_only_hiding_precommit. It does NOT compare against a fixed fixture
nonce; the nonce is absent from this verifier interface. Prover seed derivation
uses the nonce in its private generation context. This observation alone is
not a soundness attack or proof that a nonce must be a separate wire field.

The reusable core helper begin_state_only_hiding_precommit validates a nonzero
nonce and supported layout/factor fingerprints, then absorbs context.encode()
under the hiding-precommit label. Its 81-byte encoding is version1, statement32,
nonce32, layout8, factor8. `AspisV8R17/HidingContextBytes.lean` proves the length,
exact nonce slice at drop33/take32, and different-nonce distinction for encoded
contexts and their absorb preimages at a fixed state/label. Four #print axioms
audits use propext only. No hash collision resistance is inferred from distinct
preimages, and the existing helper's accepted fingerprints are not asserted
to authorize the R17 structured-G/two-channel profile.

The entropy-backed adapter must explicitly specify how the public attempt
context is authenticated/bound (possibly through an outer binding), how both
ends reconstruct the same precommit prefix, and where durable reservation and
failure reporting occur. Merely replacing deterministic_spend_fixture with
generate()/generate_for_mask_nonce() would leave that contract unproved.
Neither verifier inputs nor wire bytes were silently changed in this audit.
No wallet/account key generation or nonce-store operation was performed.

The read-only checker now pins eleven staged artifacts plus six current files
(17 comparisons), adding performance_verifier.rs and core state_only_hiding.rs.
Its exact test-shim exception is restricted to the prover file, not all files
with that basename. All comparisons pass. No old pin was waived.

| Focused target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| HidingContextBytes.lean, cached lake, -j1 -M1800 | 0 | 7.43 | 1195589632 | 0 |
| Extended oracle-entrypoint pin checker | 0 | 0.04 | 20496384 | 0 |

The Lean target emitted its matching r17 cached object and has two harmless
unused-simp warnings. No unchanged Rust/Lean regression was rerun. Existing
GatedRelease and RetryFailureBound remain conditional: a matching gate/view
transport and a source conditional success bound must be proved, not assumed
from entropy generation or the byte-framing lemmas.

Date 2026-09-21. Base `df79427f151d8b23d64c4a2f81b4b3e61c1f53f9` plus
this changeset. Scope is the selected v19 research host's mask/salt/D,
transcript and Merkle pipeline, not a complete call graph or privacy theorem.
All inspections are read-only; no production/entropy/nonce-store code changed.

## Source correspondence now inspected

The staged `performance.rs` passes the root `relation_callback.rs::hash`
callback into attempt reservation/material construction, D derivation, leaf
salts and private trees. Transcript uses that same callback. The host callback
concatenates every input slice through one SHA-256 state. The following
ordinary queries therefore belong to one byte-addressed oracle, not separate
ideal oracles merely because they are in different Rust modules.

| Operation | Actual source behavior | Required model treatment |
| --- | --- | --- |
| Positive-transfer entropy binding | Hash of legacy-mask-stream domain, frozen descriptor, binding | Public deterministic query before mask construction |
| Main mask seed | private-mask-seed domain, precommit binding, context81, field entropy32 | Secret-input query; no unconditional seed independence |
| Main mask blocks | private-mask-expand domain, seed32, counter u64 LE | Counter stream with shared word cursor |
| Source seed | pool-v1 source-seed domain, precommit binding, context81, same field entropy32 | Retain the common entropy, rather than inventing an independent seed |
| D seed/blocks | Attempt binding, D-seed domain/source seed, then profile21 source-expand stream | Same callback; separate domain strings, not a new primitive |
| Salt derivation | private-leaf-salt domain, attempt binding32, nonce32, derivation tag, index u32 LE, salt seed32 | C1/C2 share the retained salt; source tag 0x77 is not the typed-leaf tag |
| Attempt binding in salt helper | Recomputed inside every derive_pool_v1_leaf_salt call | Repeated byte address gets the same answer; distinguish calls from first assignments |
| Merkle leaves/parents | Full SHA answer, then truncate to 26 bytes | Preserve full answers in the oracle table; truncation is an observation |
| Transcript | state-prefixed absorb/squeeze/advance grammar | Retain framing overlap boundary in TranscriptAddresses.lean |

The mask builder consumes C1 cell masks, ten mask-only columns, G, then H1
padding from the same main expander. Balancing changes dependent coordinates
after draws. Used masks cannot be independently redrawn by a privacy coupling.

Both main and D expanders allow **16** attempts per M31 limb and retain the
word cursor between field draws. Transcript allows **8** attempts per limb
and discards remaining block words at the end of each QM31 call. The generic
cursor proofs take fuel explicitly and may support both; the specialized
2^-248 theorem concerns only an ideal eight-attempt limb. It is not the
source mask-expansion failure bound. Both expansion counters wrap in Rust;
distinct counter-address reasoning must justify no wrap under a source bound.

## Direct SHA and publication boundary

`DurableStateOnlyMaskNonceStore::reservation_path` directly invokes Sha256,
bypassing the supplied callback. Its input is the attempt-reservation domain
and public mask nonce; its output determines the ledger filename. If the
durable adapter is included in the complete oracle execution, include this
query too. Do not infer callback logging is a universal capture mechanism.

The selected staged fixture instead creates an InMemoryStateOnlyMaskNonceStore
and uses deterministic_spend_fixture with public fixed fixture bytes. Its
manifest explicitly enables insecure-spend-fixture. Those executions cannot
establish production entropy, durable retry accounting or publication privacy.
The two stores also enforce different scopes: the in-memory set keys on
(statement digest, nonce), while the durable filename depends on the nonce
alone. Neither behavior may be silently substituted for the other in a theorem.
No nonce store, key or ledger was created, deleted or exercised in this audit.

## Reproducible source lock and evidence

Run `python3 tools/check_r17_oracle_entrypoints.py --stage STAGE` from this
research directory (or use its repository-relative path). It pins nine staged
artifacts and five current files, printing only paths/digests and scope flags.
STAGE inspected here is `/tmp/aspis-r15-host.drHYn9/r17-two-channel-source-v19`.
The checker is read-only and fails on every mismatched digest.

Current state_only_hiding.rs is not byte-identical to the staged file. The
only diff is the exact two cfg(test) module declarations for retained R11/R13
tests. The checker verifies both distinct hashes and removes only that exact
known shim to compare the remainder; it does not ignore arbitrary test code
or waive either pin. Entropy, transcript and Merkle files match their staged
pins exactly. All expected digests are retained in the checker.

| Focused check | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Fourteen actual pin comparisons and exact shim check | 0 | 0.06 | 20463616 | 0 |

An in-memory negative control also verified that modified bytes fail the
digest check. No Rust/Lean source changed, so no unchanged compilation or
regression was repeated and no new #print axioms result is claimed.

## First remaining proposition

Refine the combined, entropy-backed source/adversary execution into the retained
causal memoized model, with all actual hash calls (not just this inspected
slice), seed relationships, bounded counters and stop/failure observations.
Then justify the first-assignment event probabilities and adaptive selection
loss. The source-map/pin checker is not this refinement, a call-count bound,
a seed-replacement argument or a simulator. The three missing nonhost
preimages remain missing; complete_generated_closure remains false.
