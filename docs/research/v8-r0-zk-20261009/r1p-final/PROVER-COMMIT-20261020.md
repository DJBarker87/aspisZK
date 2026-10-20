# Prover commitment source closure — 2026-10-20

Branch `codex/cx-prover-commit-20261020`; source revision
`6bb2b9cb1f2517b51763ed09b16b8716d3226caa`.
Adopted verifier freeze remains `b2727acd3`; the parked candidate is not used.
No production Rust or existing Lean module is changed.

## Status

STOPPED on the pinned Aeneas translation blocker below. **No requested
checklist row is discharged.** Charon lowered the actual salt cone, but
no Lean module was generated, added or compiled; attempts 8100–8399 remain unused.
Extraction uses the pinned stage2-continuation Charon/Aeneas kit on the
build host, own source/cache, optimized compilation and capped scopes.
Lean targets, if translation succeeds, use env J attempts 8100–8399 only.

## Evidence

`docs/research/100bit-spend-path-20261013/evidence/prover-commit-20261020/`.

## Source-to-definition inventory (readings, not discharged proofs)

All paths below are relative to this repository. `P` abbreviates
`docs/research/v8-r0-zk-20261009/lean/R1Z/`.
D80's actual quantified source target is `PremisesR1PBin.lean:19`
(`AddressAt`), decomposed at `:29` (`commit_bytes_iff`); it ranges over
all secrets, tapes, challenges and **arbitrary** commitment-answer vectors.
An actual successful hash trace alone does not establish this target.

| Checklist row | Actual source and matching definition | Status |
|---|---|---|
| salts | `crates/aspis-prover/src/state_only_entropy.rs:568`: validate reserved context, derive attempt binding, hash domain / binding / nonce / tag / LE32(index) / leaf secret. `crates/aspis-r1-cost-probe/src/prover.rs:189` calls for every index below FIBRE_COUNT. Model P`LayoutR1PBin.lean:140`. | Awaiting translation and address/carrier transport. |
| seeds | `crates/aspis-prover/src/state_only_hiding.rs:388` mask seed; `crates/aspis-prover/src/state_only_entropy.rs:426` source seed and `:650` D seed. Match P`LayoutR1PBin.lean:136`. The reserved object retains source seed, not raw field entropy (`:439`). | Awaiting translation. |
| reserved secret distribution | `crates/aspis-prover/src/state_only_entropy.rs:172` samples 96 OS bytes, splits nonce / field entropy / leaf secret, rejects if any is zero, caps retries. `:202` instead fixes a supplied nonce and samples 64 bytes. Model P`GamesR1PBin.lean:84` uses three nonzero coordinates. | OS law, conditioning, bounded entropy failure, reservation and caller law remain; deterministic source code cannot alone prove the OS distribution. |
| mask_expander / source_expander | `crates/aspis-prover/src/state_only_hiding.rs:340` and `crates/aspis-prover/src/state_only_entropy.rs:770`: domain / seed / LE64(counter), counter initially 0, word initially 8, refill then wrapping increment, four-byte word slices. Match P`LayoutR1PBin.lean:131` and P`FinalR1PBin.lean:44`. | No counter reuse needs an invocation bound; it is false for an unrestricted lifetime because increments wrap. No unrestricted non-wrapping theorem is claimed. |
| stream selection | `crates/aspis-prover/src/state_only_hiding.rs:447` initializes SeedExpander from the mask seed; `crates/aspis-prover/src/state_only_entropy.rs:647` initializes Profile21SourceExpander from the D seed. Actual pair-forest caller `crates/aspis-r1-cost-probe/src/prover.rs:135`; wrapper `crates/aspis-prover/src/state_only_entropy.rs:703`. | Seed 1 is intermediate input to seed 2, not a third commitment expansion stream. |
| leaves | `crates/aspis-r1-cost-probe/src/host_commitment.rs:152` lane selection; `:188` packs four points, lane order, widths 4/16 bytes; `:199` selects C1/C2 tags. `crates/aspis-r1-cost-probe/src/prover.rs:220` folded salt, `:223` packed folded values / padded zero leaves. `crates/aspis-core/src/state_only_private_merkle.rs:29` delegates to the three-slice `:42` hash. Model P`LayoutR1PBin.lean:142`; shared grammar P`SharedGrammarBridgeBin.lean:21`. | Byte grammar alone does not identify source leaf values with Pr.leafVal. |
| exhaustion | `crates/aspis-prover/src/state_only_hiding.rs:352` and `crates/aspis-prover/src/state_only_entropy.rs:785` accept a low-31-bit candidate iff < P, cap each limb at 16 tries. Model P`CommitReadsR1.lean:140`, `:145`, `:154`; required RExh at P`FinalR1PBin.lean:54`. | RExh is a one-way implication, not iff. A tapeOf instance and failure classification are required before either direction is a source theorem. |
| counters / streams / cells / blocks | `crates/aspis-prover/src/state_only_hiding.rs:450` c1 cells; `:455` ten mask-only columns; `:462` 1024 QM31 G cells; `:467` inactive H1 cells. `crates/aspis-prover/src/state_only_entropy.rs:656` 1024 QM31 D cells. Model P`CommitReadsR1.lean:289` caps L1 at 45056 and fixes L2=4096; `:210` bounds touched blocks of a successful decoded stream. | Needs universal source loop/geometry and read-completeness proofs, not fixture counts. |

The cell arithmetic is 26×1024 + 10×1024 + 4×1024 + 4×1024 = 45056
and 4×1024 = 4096. At 16 trials/limb and eight words/block the padded
worst-case block budgets are E1=90112 and E2=8192. Both satisfy
16L=8E, E=2L and E<2^64. These arithmetic readings do not supply an
`R1ProverP` instance or prove complete source-read coverage.

## Extraction stage 1: actual salt cone lowered

The extraction root is the unmodified `prover::derive_private_salts`, with
transparent dependency selection for `aspis_prover::state_only_entropy`
and `aspis_core::state_only_hiding`. It includes actual bodies for
`derive_pool_v1_leaf_salt` (LLBC function 8), `validate_pool_v1_context`
(114), `pool_v1_private_attempt_binding` (115) and context `encode` (158).
`llbc-functions.json` records all extracted names, opacities and source spans;
foreign library interfaces are not claimed proved. The model source remains
unchanged. No handwritten replacement Rust implementation is used.

Charon exit 0, wall 36.281 s, peak RSS 577276 KiB, swaps 0;
`salts-charon/receipt.json` records the exact command, environment and cgroup.
`llbc-pin.json` records the retained host artifact by hash and size only;
no binary or LLBC is committed. This is lowering evidence, not a Lean proof.
The actual Charon and extended-static Aeneas binaries are hashed in
`source-pins.json`; the kit is the one used by stage2-continuation.

The initial 8 GiB Aeneas reservation was held while other jobs occupied
the host. At a later snapshot the populated caps totalled 48.375 GiB;
Aeneas was launched with MemoryHigh=4G / MemoryMax=6G, fitting the
55 GiB limit. Charon was not rerun. The exact admitted snapshot is
`salts-aeneas-reservation.json`. `--resume-aeneas` selects the completed
Charon artifact; it is not permission to repeat the failed translation
unchanged (the receipt directory guard refuses that).

## Translation blocker and final disposition

Aeneas exits **2** after **0.459 s**, peak RSS **71808 KiB**, swaps **0**.
The diagnostic is exactly:

```
Unexpected
Source: 'crates/aspis-r1-cost-probe/src/prover.rs', lines 191:4-195:1
Compiler source: interp/InterpAbs.ml, line 191
```

`salts-aeneas/stdout.log` ends after the symbolic fixed-point context of
the `for index in 0..FIBRE_COUNT` loop, with borrowed `reserved`, `salts`,
iterator, pending return and shared usize loans. `salts-aeneas/stderr.log`
records `convert_value_to_abstractions`, `match_bottom_with_other` and
`join_ctxs.join_prefixes` in the stack. This identifies a translator
loop/context-joining failure; it does **not** establish a Rust defect or
that a particular refactor would repair it. This was not a memory failure.
No generated destination directory exists.

Per the explicit stop-on-translation-blocker instruction, no source
refactor, substitute extraction, smaller helper retry, new Lean theorem,
or privacy-root replay follows. In particular this does not close the
salts row merely because Charon could lower its code. Seeds, reserved
secret law, both expanders, leaves, exhaustion (including the requested
converse) and universal counter/stream/cell/block bounds all remain open.
The existing final privacy endpoint and its conditional premises stand
unchanged. No false deployed source target was asserted; the unrestricted
counter claim would wrap, so only invocation-bounded non-reuse is relevant.

Resumption needs a lead-authorized translator repair or prover-loop
refactor with new source/dependency pins, then actual generated proofs and
D80/wordsE/carrier joins. No such change is proposed as already validated.
The parked candidate and adopted verifier were not changed or copied in.

`attempts.jsonl` records two **extraction** steps, not invented Lean
attempts. `manifest.json` records status, commands, source revision,
source/tool hashes, LLBC hash/size, full diagnostic/log paths, limits and
empty theorem/axioms lists. `collect.py` checks the retained source hashes
and reconstructs these summaries without running tools. `#print axioms`
is not applicable because no Lean declaration was generated or claimed.
No runtime or frozen-manifest suite was needed: production source is
unchanged. No keys or wallets were accessed; no push was made.
