# Aspis one-transaction verifier: freeze record

Status: target not yet established. This note pins one source revision of the Aspis
one-transaction verifier and its Pool, the builds made from it, and what is proved, tested and
open at that revision. The freeze is a pin of the implementation. It is not a security claim.

Date of the freeze: 12 November 2026. Branch `future-version`.

## 1. What is frozen

| Item | Value |
|---|---|
| Source revision | `3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de` (`crates/`, `programs/`, `tools/` at this commit) |
| Verifier program | crate `aspis-r1-cost-probe-program` (`programs/r1-cost-probe`), linking `crates/aspis-r1-cost-probe`, `crates/aspis-core`, `crates/aspis-statement` |
| Verifier build settings | `--features aspis` on the program crate. It expands to `pool-adapter, one-tx, private-leaf-salts, fast-kmul, fast-prepared, fast-square, validated-decode, merkle-single-pass, tight-base, tight-weights, lazy-boundary, final-pair-expansion, merkle-in-place, lazy-horner, fold-shared`. Native tests and tools: verifier crate `--features "prover aspis"` |
| Pool program | crate `aspis-pool` (`programs/aspis-pool`), features `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit` (the recipe of the deployed Pool) |
| Registry and upload programs | unchanged since the earlier pin: ELFs `7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab` and `9b2ab3d41695d81bfb79b93931d9323515fcc28a35fd725253be5e41bdc45874`, as deployed on devnet |
| Build tools | `cargo-build-sbf` 3.1.13, platform-tools v1.52 (rustc 1.89.0), `--locked`, offline; client and native tools with Rust 1.94.1 |
| Proof format | 55,815 bytes, magic `ASPIS\x00\x00\x02`; 40 transcript rows, rows 0 to 32 byte-identical to the two-transaction verifier's; transcript domain strings unchanged |
| Client configuration | verifier crate feature `r1p-check` (prover on, none of the verifier build settings) |
| Lean sources | `docs/research/future-version/lean/` at the same commit; unchanged since 5bf1b2216ff, the revision of the coherent rebuild (section 3) |

The verifier ELF embeds two program identifiers at build time, the Pool's and the registry's
(`ASPIS_R1_POOL_PROGRAM_ID`, `ASPIS_R1_REGISTRY_PROGRAM_ID`). The same source therefore gives one
ELF per deployment. Two are recorded here:

| Build | Pool identifier embedded | ELF sha256 | Bytes |
|---|---|---|---:|
| Measurement build (the Pool address of the recorded devnet payments, so that they can be replayed) | 37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt | `827aaec1cbd92e37767d3d76b9fc6174ef2851a498e2e7935e1b55bc68ccb12b` | 969,328 |
| Devnet build (the new Pool program of section 8) | 4hxEyoU8MC3oFMya8D8MAcvhCPhLfHKDP1Ji9byYycn1 | `6f53dc5a923ad2beecc9ee11f59ce2f1c16ac388a82a5cfcd7855f31994d5890` | 969,328 |

The two ELFs differ in 32 bytes, the embedded Pool identifier (file offsets 0xe4bc8 to 0xe4be7; the devnet build holds there the 32 bytes of the new Pool address). Registry identifier
in both: 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q.

Pool ELF: `0553a8bd5ef5c5ff93023b1923f96f9651a23f5aa4e50855baebe29109799cec`, 340,320 bytes. The Pool embeds no program identifier.

Reproduction. Each ELF was built twice, from two copies of the source at different paths with
separate target directories, on the build host: trees `src-frz-a` and `src-frz-b`, each
made from `git archive` of the commit (`crates programs tools Cargo.toml Cargo.lock`, 1,871 files,
archive sha256 `1f0d78fba887a9da57bfec8803874dd7d4f4d43ab7803650a1e88ed6991d5b30`). The two
measurement builds, the two devnet builds and the two Pool builds each give the same hash. The
measurement ELF is also byte-identical to the ELF built from the working tree that passed the
naming gate (a third path), and the Pool ELF to the one built from the candidate tree.

Build scripts: `evidence/future-version-20261111/host/fv_frz_build.sh` (verifier; feature list and
the two identifiers are arguments) and `fv_pool_build.sh` (Pool). Records per build (exact
environment, command line, source tree hash, tool versions, ELF hash): `out/<attempt>/` on the
host, copied to `evidence/aspis-freeze-20261112/builds/`.

## 2. What changed since the devnet experiment of 11 November

The one-transaction verifier that ran on devnet on 11 November (program CmxQHrAx…, source
8a4059c8bc2) is the starting point. Since then, in order:

1. Transcript continuation and the Merkle check moved last (ONE-TX-EXPERIMENT.md round 6).
2. Seven functions rewritten so that the translation tools accept them, and the direct call of
   the runtime's hash kept (round 7; owner decision of 11 November).
3. The sampler's digit function in index-loop form (round 8).
4. Bounded optimisation of three verifier kernels (round 9; 25,991 compute units less at the
   worst case).
5. Pool: the zero check of a history page done by one overlapping comparison instead of a byte
   loop (POOL-PAGE-CHECK.md; about 66,500 compute units less when a page rolls over).
6. Translatability pass over every function the one-transaction entry reaches, in four crates
   (TRANSLATABILITY-PASS-VERIFIER.md, -STATEMENT.md, -CORE.md): the text of the two-transaction
   verifier's functions restored where the experiment had edited it, with the Aspis variants as
   separate definitions; functions the tools rejected reshaped. Cost: 386 or 387 compute units
   per payment.
7. Names (commit 3d700effcab): build settings lose the experiment prefix and the deployed program
   is built with one aggregate setting, `aspis`; the one-transaction module and its functions get
   plain names (`fused` is `one_tx`, `summed_format` is `format`, the entry is `verify`, the
   re-packer is `pack`); five undeployed experiment settings are removed with their code;
   experiment labels are removed from comments. Cost: none (compute exactly equal; every program
   function byte-identical after masking call and address immediates).

Item 1 is the last change to the protocol and the proof format. Items 2 to 7 change neither, nor
what a payment reveals, nor the prover's output. Each was adopted after the same gates (section 4).

## 3. What is proved

Model level only. `lean/AspisFailureBoundModel.lean`:

- `failure_bound40P_model`: for every decoder and every prover making at most `Q` oracle
  queries, the mean failure mass of the 40-row recorded experiment with the Aspis decision, plus
  the query-scan allowance, is at most
  `kappa(Q+1111) + Q·capMax + verifierCharge40 + 2^-126 + 2^-454`.
- `failure_le_per_query_model`: the same left side is at most `(Q+1)/2^100` for `Q ≤ 2^150`.

The only hypotheses are the bound on the prover's queries and, for the second, `Q ≤ 2^150`. The
80 proof modules were rebuilt coherently from the committed sources (host attempt RPL-c1,
manifest sha256 `fbd1b37831fc67136dbd43259d2b9619a27254ae5678f7a8767bea83347fcce7`); the theorems
print `[propext, Classical.choice, Quot.sound]`; the soundness lead's reviewer read the chain and
found it faithful (ASPIS-FAILURE-BOUND.md section 8).

This is a theorem about a model of the protocol. It does not establish the release target. Not
established, each a named obligation:

1. Source refinement: nothing compiled ties the model's decision to the Rust at the frozen
   revision. Section 5 gives the state of the translation that this needs.
2. Completeness of the model verifier (that it accepts an honest run). Argued in
   RECORDED-EXPERIMENT-40.md section 11.4, not compiled. Without it the bound is formally empty.
3. The account term (the form of the bound over the extracted entry, the runtime transport and
   the account budget).
4. The payout conjunct: a model exists (`lean/AspisPayoutModel.lean`,
   ONE-TRANSACTION-GAME.md section 11) with five open source obligations and two runtime trust
   rows (section 6).
5. The binding of the bound to the outcome of the one-transaction game, and campaign accounting
   (repeated attempts, several targets).
6. Three equalities introduced this week that hold by an argument and not by identical text
   (soundness lead, note (a) of section 9). They are to be stated as hypotheses of the source
   refinement and then proved: `extension_lane` with `scanned_k` (safe because `canonical_scan`
   has run first); `decode_lane_from_pool_release` with `lane_frontier` (all checks are made, then
   the rejection); `merged_level` (the index is read before the write in place).
7. Kernel equalities: each deployed optimised kernel of the statement crate (the `*_factored`,
   `*_packed_selector_tensor`, tensor-basis and windowed kernels listed in
   TRANSLATABILITY-PASS-STATEMENT.md section 7) owes an equality with its unoptimised kernel.
   The same holds for the three kernels of round 9 (`base_fold`, `merged_level`,
   `extension_lane`).

Privacy is a separate contract and is the privacy lead's. Nothing in this note is a privacy
result. The prover's output is unchanged by items 2 to 7 of section 2 (tested, section 4); the
privacy pin for Aspis is still to be set by that stream.

## 4. What is tested

Each verifier change of items 2 to 7 of section 2 was adopted only after the gates below on the
changed tree against the tree before it (the mutant campaign from round 7 on); the Pool change had
its own gates (POOL-PAGE-CHECK.md). The last full run is on the frozen tree itself.

| Gate | Result at the frozen revision |
|---|---|
| Unit tests of the verifier crate, deployed settings with the prover (they include the differential tests that keep each rewritten function beside its earlier form) | 56 pass |
| Client configuration (`r1p-check`), prover and simulation tests | 15 pass |
| Program crate tests, two-transaction settings | 89 pass |
| Program crate tests, deployed settings | 64 pass, 25 fail: the two-transaction verifier's checkpoint tests, which the one-transaction configuration rejects at its first stage. The same 25 fail in the candidate and in the tree before the translatability pass. Excluding them needs a test file split (open item) |
| Integration tests (nine files) | pass |
| The two recorded devnet payments replayed in one transaction each, deployed Pool | settle at 1,281,351 (transfer) and 1,287,871 (withdrawal) with the final state of the recorded run; a changed certificate and a buffer in the earlier format are rejected with nothing changed |
| The same with the frozen Pool | settle at 1,232,920 and 1,239,440, same final state. The replay tool exits with an error by design when the Pool is not the recorded one, because its two-transaction control then uses fewer compute units than recorded; every other condition it checks holds |
| Redirect attempts on the recorded withdrawal (destination replaced in the request and the account list, in one of them only, and by a third-party submitter), both Pools | every redirect rejected with nothing changed; the unchanged settlement submitted by a third party pays the recorded destination |
| Mutant campaign, 156,704 corrupted copies of the two recorded proofs, tool built from the frozen tree | verdicts identical to the candidate's, with the observer (file sha256 `e3659a53d3b4e308711668d82715cd981e8d3bdc7ba859c9ff3bdaa1e3c9e2b9`) and in the deployed configuration (verdict file `a050df4712fb841d90841914f8d528fa435da5956e2ba92da29651e078c81981`, no observer mark) |
| Prover output (worst-case tool built from the frozen tree, seven constructed payments) | proof and re-packed proof hashes equal to the candidate tool's in all seven |
| Compute against the candidate ELF | exactly equal in all seven scenarios and on both recorded payments |
| Function-level identity of the program against the candidate | all 261 functions byte-identical after masking call and address immediates (naming gate) |

One run on the frozen tree, host attempt `FRZ-checks-c1` (17 min 55 s, peak 1.6 GB, script
`fv_frz_checks.sh`, results `evidence/aspis-freeze-20261112/checks/`). Its last line reads
"status: FAILED": that is the replay tool's exit code with the frozen Pool, explained in the row
above, and nothing else. Comparison base: the candidate 33e2d8475bc, whose own gate compared it
with the tree before the translatability pass, and so on back to the build that ran on devnet on
11 November; each link was a full gate.

Compute, whole transaction, frozen verifier with the frozen Pool (LiteSVM 0.16.0, Agave 4.2.1;
`evidence/aspis-freeze-20261112/measurements/`):

| Scenario | No marker pre-funding | One-lamport marker |
|---|---:|---:|
| Withdrawal at page rollover, heaviest of 101 proofs (897 parent digests) | 1,258,313 | 1,262,410 |
| Withdrawal at page rollover, another proof | 1,247,425 | 1,251,522 |
| Withdrawal, nearly full page | 1,249,528 | 1,253,625 |
| Withdrawal, young page | 1,239,175 | 1,243,272 |
| Withdrawal at genesis | 1,242,797 | 1,246,894 |
| Transfer at page rollover | 1,239,849 | 1,243,946 |
| Transfer, young page | 1,233,894 | 1,237,991 |
| Recorded devnet transfer, replayed | 1,232,920 | 1,237,017 |
| Recorded devnet withdrawal, replayed | 1,239,440 | 1,243,537 |
| Devnet run of the frozen build (section 8) | transfer 1,234,048, withdrawal 1,238,634 | |

Heaviest measured: 1,262,410. Worst case with the allowance: 1,273,107, which leaves 126,893.
An ordinary payment leaves about 156,000 to 166,000.

The limit is 1,400,000 per transaction. Worst case: the heaviest measured case plus the
arithmetic allowance of WORST-CASE-COMPUTE.md (10,697, fitted for an earlier build and kept as an
upper allowance). These are measurements on constructed and recorded payments, with an analytical
allowance. They are not a formal cost bound.

Checks by the other two leads, as reported by them:

- Privacy lead: prover harness, 300 cases including 120 failing attempts, against its baseline of
  the two-transaction pin. On the candidate
  33e2d8475bc: 300 of 300 identical (180 accepted, 30 entropy rejections, 60 semantic rejections,
  30 attempts exhausted), re-packed proofs 180 of 180 identical. Its three pre-freeze checks on the
  same commit: the client configuration resolves to the same features as at the pin; the
  whole-tree text count of section 5; a reading of both bodies of all 16 changed functions, with
  no difference found in operator kind, order of effects, loop bounds or iteration order for the
  five the prover reaches, and no difference in returned or error values for the other eleven.
  Its notes: `low_base_p_digits` lost two `debug_assert!`; the checkpoint decoder now reads all
  eight lane sequences before testing them (same error value and position); `claims` allocates
  through `heap::filled` instead of `heap::uninit` (one request, same size). Not decided by it:
  whether a new item shadows a name an unchanged function resolves, the other new functions, and
  macro-generated code. A condition it sets, which is part of this freeze: the client
  configuration is `r1p-check` alone, so that the three multiplication functions
  (`QM31::mul`, `QM31::square`, `PreparedQm31Multiplier::mul`) are the pin's arithmetic in the
  prover; the settings `fast-kmul`, `fast-square`, `fast-prepared` and the aggregate `aspis` are
  never on in a client or prover build. It reruns the harness on the frozen commit; that result
  is not in yet (section 10).
- Soundness lead: its reviewer read the whole diff of the translatability pass
  (7dffe3e2a93..33e2d8475bc) and found no behaviour change in any changed function.
  It then read the freeze commit 3d700effcab line by line: every changed line is a rename from the
  map, a respelled cfg, a comment, or code removed with a deleted setting; none of the five
  deleted settings was in the deployed, two-transaction or client configuration; no behaviour
  change beyond the reviewed candidate. Its addendum is at
  `~/aspis-lead-infra/ASPIS-FREEZE-DIFF-REVIEW-20261112.md` (the soundness lead's file).

## 5. Translation of the source (state of the refinement input)

The refinement of section 3, item 1, needs every function on the on-chain path translated to
Lean by the Charon and Aeneas tools, or covered by a named boundary. One release-style emission
of the frozen tree, under the deployed build settings, second tool pair (Charon 454586e9, Aeneas
0d21a9ec, `-abort-on-error`): `evidence/aspis-freeze-20261112/emission/`.

| Scope | Rows | Translate and the Lean elaborates | Translate, Lean does not elaborate | Opaque: named gap | Opaque by the scope's configuration |
|---|---:|---:|---:|---:|---:|
| Verifier crate | 200 | 199 | 1 | 0 | 0 |
| Program crate | 57 | 51 | 0 | 6 | 0 |
| Statement crate (semantic side and account decoders) | 287 | 283 | 0 | 0 | 4 |
| Core crate | 122 | 116 | 1 | 3 | 2 |
| All | 666 | 649 | 2 | 9 | 6 |

Both Aeneas runs with `-abort-on-error` exit 0 in every scope (host attempt `FRZE-frza`, 13 min
34 s, peak 3.6 GB). The rows that are not "translate and elaborate":

- Translate, do not elaborate (library models missing): `compact::expand_values` (zipped chunk
  iterators) and `r0::heap::filled`.
- Named gaps, which the tools reject and the run declares opaque: in the program crate
  `close_checkpoint`, `lifecycle_init`, `lifecycle_write`, `lifecycle_finalize` and the two
  compile-time program identifier constants; in the core crate `CM31::inv` and `CM31::inv_with`
  (a function passed as a value; the two-transaction proof covers them through its first tool
  pair) and `heap::uninit` (raw-pointer allocation).
- Opaque by configuration, as in the workers' runs: the four payment-relation encoders and
  decoders in the decoder scope, for which no release-style emission exists, and `M31::inv` and
  `QM31::inv`, which the core worker's separate run translates and elaborates.

The same run on the candidate tree 33e2d8475bc gives the same outcome for every row through the
rename map (669 table rows on each side, none on one side only; two rows change class only,
`EbyKDot::push` and `validate_record_fields`, now identical to the pin without an attribute).
On the candidate tree the emitted files are byte-identical to the three workers' own emissions,
and all 668 of their rows keep their outcome.

Checks for the translator defects that exit 0: no silent omission of a declaration in the
verifier, program or decoder scopes (in the statement semantic scope three derived `clone`
functions of the core crate are not emitted; they are rows of the core scope); every function
with a body and no emitted definition is a derived `Clone` or drop glue; no reversed mutable
iterator on the linked path (the erased-region scan finds none, and by the verifier note this
tool pair cannot produce that shape, so the scan's zero is not evidence by itself; the source
search finds the construct only in a comment, in three test sites and in an unlinked function).

A translated function is not a verified function. The emission is the input to the refinement
proof; no theorem about the emitted code exists yet beyond what the two-transaction proof already
has for the functions whose text is identical.

Function text against the two-transaction pin c7593d23fdc (verifier crate and program crate;
`translatability/verifier/tools/TP_fntext.py`): 712 identical, 9 identical under an added cfg
attribute, 10 changed, 166 not present at the pin (data: `evidence/future-version-20261111/host/fv_fz_fntext_after.json`).
Over the whole tree the client compiles (ten crates; the privacy lead's token-level tool, run on
33e2d8475bc): 4,402 identical, 6 identical under an added cfg, 3 that keep the pin body under a
cfg that is off, 16 changed, 104 new, none removed. The 16 changed: the two sampler functions
(`low_base_p_digits`, `add_small_base_p`), `prepared_claim`, `Prepared::new`, `canonical_scan`,
`QueryGeometry::for_range`, `wide_view`, `claims`, `WideExact::to_le_bytes`,
`external_linear_lazy`, `composition_parts`, `validate_master` and four account decoders. Text identity is what lets the
existing Rust-to-Lean link of an unchanged function be reused; the functions that changed or are
new carry no such link and are listed in the three pass notes as "reshaped" or "new gate".

Named gaps in the program crate (TRANSLATABILITY-PASS-VERIFIER.md section 6):
`close_checkpoint` (reachable; writes lamports and data through the SDK's account handles; a hand
model is owed, as for the two-transaction verifier), the three lifecycle functions and
`lifecycle_accounts` (not reachable in the deployed program: the route admits only the
settlement, the Pool request and the checkpoint close), the compile-time decoding of the two
program identifiers, `compact::expand_values` (translates; library models for the zipped chunk
iterators are missing), and the hash call (runtime boundary, section 6).

## 6. Trust rows

Only runtime, SDK and standard-library items are trust rows (owner rule of 10 November). No Aspis
code is assumed correct, with one exception decided by the owner on 11 November and named here:

- **The hash.** The verifier calls the runtime's SHA-256 directly
  (`solana_program::syscalls::sol_sha256`, `programs/r1-cost-probe/src/lib.rs` line 24, three
  lines). The trust row is "the runtime's SHA-256 syscall computes SHA-256 of the concatenated
  parts", and it includes this call site: that the pointer, the count and the output buffer are
  passed as the syscall expects. The SDK's own wrapper was measured and costs 24,618 compute
  units more per payment.
- **R-a, post-call visibility.** After a cross-program invoke returns, the caller reads the
  callee's writes to the accounts it passed.
- **R-b, writable set.** A cross-program invoke changes only accounts passed to it as writable.
  Both are rows of the payout conjunct (ONE-TRANSACTION-GAME.md sections 10.5 and 11).
- The rows the two-transaction contract already has: the Solana runtime's execution of the
  program, account ownership and signer checks, the clock sysvar, the compute meter, the standard
  library items named by their contracts (slice equality, which the Pool's page check now uses,
  is among them), and the compiler.

## 7. Compute cost of the translatability work, and one judgement call

The owner's standing rule for recommendations is no compute up, no soundness down, no privacy
risk. On the night of the freeze the lead relaxed "no compute up" for translatability rewrites
to a budget of 300 compute units per reshaped function and about 2,000 per crate group, after
rounds 9 and the Pool change had freed about 92,000. This was the lead's call, made while the
owner was asleep, and is reported as such. What was spent:

| Change | Compute units per payment |
|---|---:|
| Sampler digit function, index-loop form (round 8) | +137 |
| Verifier crate and adapter: restoration of the pinned text | -3 |
| Verifier crate and adapter: reshaping batch (of which `prepared_claim` in the split form the existing proof models: +837; `canonical_scan` written out per slot: -771) | +190 |
| Statement crate, semantic side (`external_linear_lazy` +102, `pattern_values_windowed` about -43, `composition_parts` -166) | -107 |
| Account decoders | +307 |
| Core (`WideExact::to_le_bytes`) | 0 (ELF identical) |
| Total of the pass against the tree before it | +386 or +387 |

One function exceeded the per-function budget: `prepared_claim` (+837). Three texts were
possible: the experiment's own (not allowed: a build-setting test inside a function of the
two-transaction verifier, and not translatable), the pinned text (+1,845, not translatable), and
the split form from which the existing proof's model was emitted (+837, translates). The third
was taken. The owner's later message "3rd option" is read by the lead as confirming it; that
reading has been stated back to the owner and not yet acknowledged.

## 8. Devnet

Deployed and run on 12 November 2026 (owner approval of 11 November for devnet).
`evidence/aspis-freeze-20261112/devnet/README.md` has the full record.

| Item | Value |
|---|---|
| Verifier | 8EEVxFAXz9BSg5LKaBxRfTbSK5xZyFrshLfKQRASvvNC, immutable, payload equal to the devnet build of section 1; 4,925,065,080 lamports locked |
| Pool (a new program; the Pool the two-transaction run uses is not touched) | 4hxEyoU8MC3oFMya8D8MAcvhCPhLfHKDP1Ji9byYycn1, upgradeable with the payer as authority; 1,729,704,440 lamports, recoverable |
| Transfer | settled in one transaction, 1,234,048 compute units, signature 2UN82ys58uXKAWWRovbYpxb4mp8nrPKNkZE5ViCR24ugcW7jfKeqEcYQT742Gs5zqrcr6VoqRsfJMGYqtpZCzcht |
| Withdrawal | settled in one transaction, 1,238,634 compute units, signature 2x4Hy6bA8wcEMHHtYiv98RRvUi73aT2YZpfojbnba3jT1NvRMNiHwHnqRxcnnTiL6pXbBmGwhLGci4kFLfmyCa8J |
| Rejected, nothing changed | a changed certificate byte and a changed Merkle node byte before each settlement; a replay after each; for the withdrawal, the destination replaced in the request and the account list, in the account list only, and in the request only |
| Predictions | eight, committed before the first signature; all met |
| Cost | per payment 1,706,880 lamports of marker rent and 275,000 of fees (18 transactions, one signed by the payer); the run with its tests and fixtures cost 137,132,000 lamports outside the deployments; payer at 18.816106048 SOL |

Before the devnet run the same sequence ran on a local validator with the candidate build and the
new Pool at its new address (host run `frzlocal2`). The
same sequence with the frozen artifacts themselves (host run `frzlocal3`) could not get host
slots in time and finished after the devnet run: complete, transfer 1,230,648, withdrawal
1,241,664, the same rejections. So the devnet deployment was made on the strength of the
candidate's rehearsal plus the function-level identity of the frozen program with the candidate,
not on a rehearsal of the frozen bytes; that was a call to save about twenty minutes.

The Pool's changed page check uses one comparison of two overlapping regions of the same account.
It ran in the Pool initialize on the local validator and on devnet.

These are test transactions with fixture witnesses on a test cluster. Mainnet deployment has not
been discussed and is not approved.

## 9. Notes from the soundness lead's review, and names

Its five notes on the diff of the pass, as received:

(a) Three equalities rest on arguments (section 3, item 6); they are to become stated hypotheses.
(b) `QM31::mul`, `QM31::square` and `PreparedQm31Multiplier::mul` are "identical under an added
    cfg": the pinned text is unchanged and selected when the fast-multiplication settings are
    off. Identity up to an enclosing cfg counts as identity.
(c) Further same-behaviour changes to be listed as new gate, not as unchanged: `coefficients`,
    `k_of`, the cfg splits of `batch_tree`, `semantic_boundary`, `decode_k` and `KbyKDot::push`,
    the observer type, the split of the one-transaction entry into an observed and an unobserved
    function with `prepare` and the finishing function; the profiling setting of the program
    crate pulls in the observer setting; `observer()` returns nothing unless profiling is on.
(d) The build of this source WITHOUT the Aspis settings differed from the two-transaction ELF in
    two functions' sizes, probably because the one-transaction module compiled unconditionally.
    Tested at the freeze: with the module behind a setting the two-transaction build still differs
    from the deployed two-transaction ELF (1,570,048 bytes against 1,567,992; 17 functions differ
    in bytes and 11 exist on one side only: the reshaped functions, the sampler, `decode_k` and a
    few statement decoders). The module accounts only for `finish_relation` and
    `finish_relation_round`. The gate is therefore not in the freeze. In the soundness lead's
    words: ELF identity to PIN2 is not available from this tree; the PIN2 link is function-text
    identity on the 721 keys plus the 10 reviewed changed functions. This note makes no claim
    that the two-transaction ELF rebuilds from the frozen tree.
(e) `WideExact::to_le_bytes` is recorded as a reshape (same ELF).

Names. The owner asked on 11 November that experiment labels be removed from identifiers at the
next build. Done in the freeze commit for
build settings, the one-transaction module and its functions, and comments (map of 66 rows:
`evidence/future-version-20261111/host/fv_fz_rename_map.tsv`). NOT done, on the soundness lead's
advice: the two crates `aspis-r1-cost-probe` and `aspis-r1-cost-probe-program`, their directories
and the `r1_*` modules keep their names, because every name in the existing Lean proof of the
unchanged functions is keyed on them; a rename would need a recorded name map applied to every
reused proof module. The deployed program file is therefore still
`aspis_r1_cost_probe_program.so`. This is an open decision for the owner (section 10). Also
unchanged: the transcript domain strings (owner decision of 11 November), tool file names and
the keys of tool output files (they label existing evidence), and a few test strings.

## 10. Open items for the owner

Decisions that are the owner's:

1. **Crate names.** A: keep `aspis-r1-cost-probe` and `aspis-r1-cost-probe-program` (never seen
   on chain or by a user; the deployed file keeps that name). B: rename them too, as its own commit
   with a recorded name map, before further Aspis proof work; this moves the pin (new ELF, new
   devnet deployment, the gates and both leads' checks again). The lead recommends A. The freeze
   was made on A without an answer, because A changes nothing that B would not also change.
2. **The compute budget for translatability rewrites** (section 7) was the lead's call during the
   night. If the owner's rule "no compute up" was meant strictly, the reshaping batch can be
   reviewed function by function; the largest item is `prepared_claim` (+837).
3. **The reading of "3rd option"** as the split form of `prepared_claim` (section 7).
4. **The new Pool on devnet is a new program**, not an upgrade of the Pool the two-transaction run
   uses. Its rent (1.73 SOL) can be recovered by closing it; the lead will not close anything
   without being asked.

Conditions and work still open at the freeze:

5. **Privacy lead's harness on the frozen commit.** It ran on the candidate (300 of 300). The
   rerun on 3d700effcab was started when the commit was sent and had not reported when this note
   was written. A difference there would void the freeze; the naming commit changes no compiled
   prover code path (client features unchanged, prover output identical in the lead's seven
   scenarios), so none is expected, but it is not in hand.
6. **Everything in section 3 under "not established".** The freeze fixes what those obligations
   are about; it closes none of them.
7. **Privacy pin.** The privacy stream sets its Aspis pin and regenerates its extraction from
   this commit; its prover-only rewrite branch (`codex/pv-aspis-rewrite-20261111`) rebases onto it.
   That branch touches no on-chain program source; merging it later changes the client only and
   needs its own byte-identity gate.
8. **Client entry `prove_for_proof_account_nonces`** (added on that branch beside the existing
   entry): whether the existing entry is redefined over it is a client decision, not part of this
   freeze.
9. **Tests.** 25 two-transaction tests of the program crate fail under the deployed settings
   (section 4). Excluding them cleanly needs `r1_checkpoint_tests.rs` split in two; a cfg attribute
   alone would also drop tests that pass.
10. **Hand model of `close_checkpoint`** and the library models `compact::expand_values` needs
    (section 5).
11. **Labels left in tool files** (file names such as `fused_probe.rs`, output keys such as
    `summed_proof_sha256`, the route label in the devnet receipts). They label existing evidence
    and are not in the deployed program.
12. **Mainnet.** Not discussed, not approved, and not supported by anything here.

## 11. Where the evidence is

- Builds, measurements, emission, devnet receipts of the freeze: `evidence/aspis-freeze-20261112/`.
- Gates, mutant campaigns, replays, worst-case runs, the coherent Lean rebuild:
  `evidence/future-version-20261111/` (subdirectories named in the notes above).
- Notes: this directory. The proof: ASPIS-FAILURE-BOUND.md, RECORDED-EXPERIMENT-40.md,
  ONE-TRANSACTION-GAME.md. Compute: ONE-TX-EXPERIMENT.md rounds 7 to 11, WORST-CASE-COMPUTE.md,
  OPTIMISATION-ROUNDS.md, POOL-PAGE-CHECK.md. Translation: EXTRACTION-PROBE.md and the three
  TRANSLATABILITY-PASS notes.
