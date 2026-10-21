# Prover commitment continuation 11 — 2026-10-21

Branch `codex/cx-prover-commit11-20261021`, base `8e4931b1f`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit11-20261021/`.

CallerLaw is proved for the fixed operational-reference decoder and removed
from a new headline by a deletion-only diff. Complete shipped outer-caller
transport and all-family shipped read coverage remain open. The focused P6
scalar-contract formulation exceeds its bounded proof gate; no new Rust
contract is adopted.

## Stage 1: byte loads and global cache

`ProverCommitOwnedBytes.readBlock_byteWord` identifies the exact extracted
four-byte load. `ProverCommitOwnedByteValue.fromLEBytes_value` proves the
little-endian numeric identity by induction on the byte list; `blockW_value`
and `byteWord_answer` identify it with the existing finite word equivalence.
No allocated stream or large numeral is evaluated.

`ProverCommitOwnedCache.next_cache` proves that each successful next-word call
preserves the identity of the cached block with the preceding answer from
the same finite oracle, and returns precisely the `wordsE` word at the current
position. Initial cache validity is unconditional. This proof includes the
refill and cached cases and retains the existing counter-capacity bound.

Accepted focused targets: J8329 (byte loads), J8332 (byte values), J8335
(cache and stream correspondence). Each exits 0, zero swaps, with only the
standard three axioms. Exact targets, source hashes, dependency fingerprints,
source revision, walls, peak RSS and all axioms/errors are in `lean/` receipts.
Drafts J8327–8328, J8330–8331, J8333–8334 are excluded elaboration failures,
not memory failures. No resource cap or recursion/heartbeat option is raised.
Only new worker-owned module/objects are installed in Env J; overwritten
versions of those modules/objects are snapshotted under this branch's host
workspace. No peer-owned source is changed.

## Stage 2: complete reference CallerLaw

`ProverCommitOwnedSequence` erases only the operational error/state wrapper
and proves that the exact extracted collector obeys the consuming word-loop
recurrence. `ProverCommitOwnedModel.sequence_model` proves equality with
`decodeWords` by induction on remaining words, using Stage 1's exact cache
law and the explicit retry budget. Both rejection and early acceptance
preserve the same suffix of one global finite oracle.

`ProverCommitOwnedArrayLaw.samples_array` transports the resulting list
equation to the actual finite arrays, proving lookup correspondence rather
than treating a default value as a sampled coordinate.
`ProverCommitOwnedCallerLaw.rawArrays_model` composes the two protocol-sized
streams. `quotient_decoder` gives the exact quotient equation, with the
identity coordinate equivalence. `ProverCommitOwnedEndpoint.caller_law`
constructs CallerLaw for precisely the fixed operational-reference prover
of `PrivacyR1HeadlineOwned`, with no new hypothesis.

Accepted focused attempts J8337, J8340, J8343, J8344, J8348 all exit 0,
zero swaps, standard axioms. Their thirteen new theorem audits are recorded
in the receipts. Excluded drafts have changed-source replacements; none
failed from memory pressure. No shipped Rust source or ELF input changes.

**Scope:** the mathematical CallerLaw for the fixed decoder is now proved.
This does not construct either shipped execution join, certify the actual
outer material-building loops, or prove all-family shipped callback coverage.
The existing headline is deliberately unchanged until those source gates
are addressed.

## Stage 3: bounded proof windows and premise deletion

`ProverCommitOwnedWindow.scalarFinite_window` proves that the operational
scalar computation depends only on the retained global answers at refill
positions inside its remaining word interval. `scalar_window` applies this
to all sixteen tries. `scalar_block_window` bounds that interval by three
aligned blocks. This is a restriction of one global oracle, not a fresh
independent ROM at each call. It gives the support condition a local Kani
window must satisfy; it does not assert that a shipped outer caller has
already supplied that condition. J8349 checks the three support lemmas;
J8350 adds the block-count bound. Both pass, standard axioms, zero swaps.

`PrivacyR1HeadlineOwnedClosed.privacy_headline_owned_closed` applies the
proved reference CallerLaw to the same D112 specialization. All other
premises, games, simulator, error and < 2^-100 conclusion are unchanged.
The original endpoint remains available. J8351 passes both audits (the
private CallerLaw application and the new headline), standard axioms,
zero swaps. It does not certify either retained shipped execution join.

The complete verbatim endpoint texts are `headline-before.lean.txt` and
`headline-after.lean.txt`; `headline-deletions.diff` contains precisely two
deleted lines and no additions. Both texts share the separately proved
CallerLaw application, so the theorem body is literally unchanged.

Verbatim before (declaration prefix):

```lean
theorem privacy_headline_owned_closed
    (builder_premises : BuilderPremises h B x)
    (R_commit_caller : ProverCommitCallerInstance.CallerLaw
      (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)))
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
```

Verbatim after (declaration prefix):

```lean
theorem privacy_headline_owned_closed
    (builder_premises : BuilderPremises h B x)
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
```

The argument name in the unchanged proof resolves to the checked private
theorem, rather than to a caller-supplied hypothesis. This is a deletion
at the fixed operational-reference endpoint; no whole-shipped-execution
certificate follows from this deletion alone.

## Stage 4: canonical global-to-local rebasing

`ProverCommitOwnedRebase.windowAnswers` constructs each nine-answer local
table as a restriction of the retained global answers. `windowHash_at` proves
the callback identity at every in-range request. `window_wrapping_offset`
proves that the Rust local-ROM wrapping subtraction is ordinary subtraction
inside these windows. `scalar_rebase` removes the support premise from
Stage 3 by constructing the correct local backend. `scalar_window_offset`
places the current counter at offset zero or one, inside the scalar contract
margin. Global allocation and counter bounds exclude wraparound.

`ProverCommitOwnedWindowCollection.collect_rebase` then proves the complete
collection equals per-scalar rebased calls, by symbolic induction, including
partial Rust error states. Each call uses a bounded local backend; every
window is derived from the same global input. No full array is supplied to a
nine-block ROM. No fresh independent table is substituted for a retained
global answer. J8352 checks the initial three rebasing lemmas, J8353 the
final four, J8354 the collection induction: all exit 0, standard axioms,
zero swaps. Source identities, dependencies and resource fields are in
the verbatim receipts.

This is the mathematical rebasing bridge for the P6 route. It does not
itself prove the actual material builder's loop schedule, entry-point
transport, or all-family shipped callback coverage.

## Frozen formal audit

`manifest.json` pins the 13 adopted Lean modules and the launch/validation
inputs. Preflight source/receipt/dependency/deletion checks pass before the
single combined replay. **J8355**, exact target **R1Z.ProverCommit11Audit**,
imports the accepted part-10 audit cone plus all adopted part-11 modules:
exit **0**, wall **2.51 s**, peak RSS **4,081,116 KiB**, **zero swaps**,
source revision **31666e439** plus the literal additive audit source identified
by SHA-256 in the receipt. The exact dependency fingerprint is retained.
All **32 public** axiom audits contain only a subset of `propext`,
`Classical.choice`, `Quot.sound`; the private CallerLaw application is
separately audited in J8351 with the same restriction. All 33 new theorem
audits therefore have explicit resource/source evidence.

The final evidence-only validator adds a whitelist check for the approved
axioms and checks the exact final audit target list. The pre-audit manifest
is retained as `preflight-manifest.json`; all Lean source identities remain
unchanged. `harness/validate.py` passes after receipt collection. This does
not repeat the Lean replay. Attempts are consumed through **8355**; next
available **8356**.

## P6 source gate: demonstrated contract-formulation obstruction

The next source consumer is the adopted masked-attempt path in
`crates/aspis-r1-cost-probe/src/prover.rs`:
`prove_masked_retrying_with → prove_masked_attempt → prove_masked_with_attempt`.
Its mask path reserves the nonce, calls
`build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref`, then
`build_mask_material_for_layout`, then the verified SeedExpander scalar/tower
callers. The D path calls `derive_pool_v1_pair_forest_zero_factor_d →
derive_pool_v1_zero_factor_d → Profile21SourceExpander`.
`source-boundaries.json` is an explicitly unproved, hash-pinned source census.
The lower-level `aspis_prover::r0::r0_prove` accepts supplied masks; it is not
the masked-attempt entry point.

The source experiments add proof-only scalar/tower contracts and
`proof_for_contract` harnesses. No whole array is checked with the nine-block
ROM. Three initial launches stop during metadata loading because the isolated
workspace initially lacks path dependencies; the complete manifest/path graph
is then copied from the pinned predecessor workspace. Those exits are not
proof failures. The initial source inventory's 484 Rust/Cargo inputs match
the host snapshot; the individual launches additionally pin their literal
input hashes.

The first general scalar contract (`mask-scalar-contract-v4`) reaches CBMC
but times out at 600.347 s (exit 124). Two changed-source offset-zero trials
are deliberately stopped to replace duplicate pure-model expansion and then
repeated callback-body expansion: `mask-offset-0-v5` exits 143 after
356.779 s; `mask-offset-0-v6` exits 143 after 440.655 s. These are excluded
trials, not passed certificates. The next version checks offset zero using
both `stub_verified(SeedExpander::next_word)` and
`stub_verified(expander_query)`, retaining unwinding/safety checks and the
same 6G/8G/no-swap/64-task scope. The expected time is explicitly compilation
and CBMC proof, not native arithmetic.

The fully summarized offset-zero case (`mask-offset-0-v8`) also times out:
**exit 124, 600.174 s**, **6,612,361,216 bytes cgroup peak**, **zero swaps**.
The retained Kani metadata confirms all three verified summaries are active:
`SeedExpander::next_word`, the extracted reference `next`, and
`expander_query`. The previous two-summary offset-zero case times out after
600.517 s. A Kissat comparison is stopped after observing that CBMC has not
yet started a SAT-solver child; it supplies no solver verdict. The final
source change adds the reference-next verified summary. No cap is raised,
no memory-pressure failure is rerun, and no whole-array nine-block check is
attempted.

This is a demonstrated obstruction to this **whole scalar postcondition
formulation within the 600-second gate**, not a counterexample to the source
equation, a proof that P6 is impossible, or an accepted contract. A proposed
replacement is a scalar rejection-prefix/closed-form cursor invariant and
one-iteration proof, followed by the already checked global rebasing and
collection induction. That replacement is not implemented here. The new
scalar and tower contracts cannot be used as verified outer-caller stubs.

All source trials are **excluded**. Literal candidates are under
`rust-drafts/`; each trial has input hashes and verbatim scope/time/stdout/
stderr receipts. Deliberate stop records identify only this task's processes.
GNU time's small parent RSS on timeout/termination does not measure CBMC's
resident set; the retained **cgroup memory peak is authoritative**.

| Trial | Exit | Wall (s) | Cgroup peak (bytes) | Swaps |
|---|---:|---:|---:|---:|
| `mask-offset-0-kissat-v7` | 143 | 226.725 | 6562865152 | 0 |
| `mask-offset-0-v5` | 143 | 356.779 | 6585774080 | 0 |
| `mask-offset-0-v6` | 143 | 440.655 | 6741364736 | 0 |
| `mask-offset-0-v7` | 124 | 600.517 | 6708785152 | 0 |
| `mask-offset-0-v8` | 124 | 600.174 | 6612361216 | 0 |
| `mask-scalar-contract-v1` | 1 | 0.048 | 11386880 | 0 |
| `mask-scalar-contract-v2` | 1 | 0.054 | 13479936 | 0 |
| `mask-scalar-contract-v3` | 1 | 0.049 | 16859136 | 0 |
| `mask-scalar-contract-v4` | 124 | 600.347 | 6681665536 | 0 |

`harness/validate-rust-trials.py` verifies every captured Rust input hash
against the baseline or a literal excluded candidate, the exact scope
limits, four compiler jobs, linker flag, unwinding assertions, zero swaps,
and the final three-stub metadata. This is evidence validation, not a new
Kani proof or a replay.

## Final adoption boundary

No Rust/Cargo/program source change is retained. `adopted-rust-identity.json`
checks the four edited trial files byte-for-byte against `8e4931b1f` and
records an empty adopted Rust/Cargo/program diff. The part-10 frozen ELF
inputs therefore remain unchanged; no unchanged SBF regression is rerun.
No ELF, object, LLBC, archive, wallet or key is committed or cleaned up.
Compiled caches are retained.

Completed: cache and little-endian load correspondence with `wordsE`, full
finite consuming scalar-array refinement, exact CallerLaw at the fixed
operational-reference endpoint, canonical consistent global-to-local proof
windows and complete rebased collection induction, and the two-line
CallerLaw premise deletion in the new headline. All 33 new Lean theorems
have standard-axiom/resource/source evidence; the single frozen combined
audit passes.

**Still open:** the actual shipped entry-point/outer-producer execution
transport, verified scalar/tower/outer function-contract composition, and
all-family shipped callback completeness (binding, mask/source/D seed derivations,
both streams, salts, leaves, nodes and transcript/retry reads). The fixed
reference CallerLaw is not a complete shipped-source certificate. Both
execution joins and the builder premise remain in the headline. No complete
shipped-source checklist row is marked closed.

No peer-owned SourceIdentification, RustRuntimeJoin or PrivacyR1FinalRelease
file is edited. No push or merge is performed. Env J attempts are consumed
through **8355**; next available **8356**.
