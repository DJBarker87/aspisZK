# Prover commitment continuation 13 — 2026-10-21

Branch `codex/cx-prover-commit13-20261021`, base `9f6852af9`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit13-20261021/`.

The builder premise is discharged on the explicitly fixed canonical admitted
domain. Both shipped scalar return/state laws, stream conversion/formatter
safety, full query-caller transport around its sampler cut, and several seed
and outer hash frames are checked. The successful source-seed wrapper,
complete material/D/tree/retry execution transport and all-family shared-oracle
coupling remain open. **The actual release target is not yet established.**

## Stage 1: explicit canonical admitted-domain endpoint

`ProverCommitAdmittedEndpoint` extends the `PrivacyR1HeadlineOwnedClosed`
namespace with an explicit `Admitted` endpoint. Its `input` is fixed to
`BuilderSource.prover`: the M31 public/witness pairs satisfying the embedded
`RspendPlus` relation, the canonical extracted merged trace, and S2 transport.
It does not claim that a shipped Rust runtime record has been identified
with that instance. That source identification remains peer-owned and open.
The original arbitrary-input endpoint is unchanged; the part-12 counterexample
remains valid there.

`Admitted.builder_premises` is proved from D96's canonical builder theorem;
`PhaseWireLog2Bin.honest` changes no public or build projection. The specialized
endpoint initially retains the premise to make the subsequent deletion-only
change reviewable. J8364 is an excluded missing-CharP elaboration draft.
J8365 passes the focused endpoint and all three printed axiom audits using
only the standard three axioms: exit 0, wall 6.97 s, peak RSS 4159700 KiB,
zero swaps. Exact source/dependency hashes and source revision are in the
receipt. No package-wide build or unchanged regression is run.

The canonical builder theorem now uses an implicit statement parameter, so
its name resolves to the proved theorem after deleting the identically named
premise. J8366 is an excluded doc-comment placement draft; J8367 checks the
specialized before statement (exit 0, 6.82 s, 4158164 KiB, zero swaps).
J8368 checks the deletion-only after statement (exit 0, 6.71 s, 4161568 KiB,
zero swaps), with all three audits standard-axiom only.
The full verbatim texts are `headline-specialized-before.lean.txt` and
`headline-specialized-after.lean.txt`; `headline-deletions.diff` deletes exactly
one binder, with no other change:

```lean
-- Before (verbatim)
theorem privacy_headline_admitted
    (builder_premises : BuilderPremises h B x)
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
```

```lean
-- After (verbatim)
theorem privacy_headline_admitted
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
```

This is genuine discharge on the explicitly fixed canonical domain. It is a
specialization of the previous arbitrary-input theorem, not a weakening with
unchanged quantifiers. The experiment, error bound and remaining real/ideal
execution-join premises are byte-identical between the two specialized texts.
No runtime join or successful-source admission proof is added or hidden.
Shared Env J drafts/objects were snapshotted under this branch's own host
directory before replacement; no peer-owned module was replaced.

## Stage 2: actual stream panic and formatter safety

The actual `SeedExpander::next_word` and `Profile21SourceExpander::next_word`
bodies run with arbitrary seed, counter, buffered bytes and `word <= 8`,
including counter wraparound and buffer reload. Constructor `word = 8` is
inside this domain; the checked postcondition retains `1 <= word <= 8`.
The oracle table holds arbitrary answers; this is a deterministic bounded
expander oracle, not a SHA-256 or probability assumption.

Two checks run each body without a formatter stub, retaining all Kani safety
and unwinding checks. Two subsequent checks use
`#[kani::stub(<core::array::TryFromSliceError as core::fmt::Debug>::fmt,
formatter_never)]`. The replacement first asserts false and then diverges:
reaching it fails verification, rather than assuming the path unreachable.
Thus the stub does not erase a reachable error. The slice is always exactly
four bytes and within the 32-byte block. These Kani checks avoid adopting
part 12's forbidden extracted Formatter dependency; no tainted Lean theorem
is imported as justification.

| Exact suffix under `safety13` | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| `state_only_hiding::...::mask_next_no_panic` | 0 | 8.920 | 551672 | 0 |
| `state_only_entropy::...::source_next_no_panic` | 0 | 11.295 | 659604 | 0 |
| `state_only_hiding::...::mask_next_no_formatter` | 0 | 10.874 | 659256 | 0 |
| `state_only_entropy::...::source_next_no_formatter` | 0 | 11.113 | 659340 | 0 |

Receipts record complete names/commands, source hashes, cgroup peaks,
6G/8G/no-swap/64-task limits, and required linker flags. `#print axioms` is
not applicable to Kani; the only new Lean endpoint remains standard-axiom
only. Expected time is compiler and bounded-verifier work, not native dense
arithmetic. The actual Rust bodies are unchanged in the proof snapshot;
only proof harnesses are appended. No production Rust/Cargo file is edited.

The first draft omitted the next-word contract's table-domain setup and
failed its precondition (not a protocol counterexample). The second failed
an unwind check in `memcmp` because 34 was shorter than a domain string;
the accepted replacement increases only the harness's unwind bound to 84.
Exact excluded and accepted text snapshots are retained. No failed safety
check is treated as a success. Host sources and caches are cloned from
part 12; replaced sources use atomic rename to preserve the predecessor.

This closes these two local conversion/panic paths. It does not prove every
formatter or panic path in the entire shipped outer prover unreachable.
Subsequent stages below establish the actual scalar result/state laws and
the complete query caller cut; the outer material schedule remains open.

## Stage 3: full query caller around the sampler boundary

`transcript::query13::result_and_retained_state` executes the complete actual
`Transcript::queries` method, rather than the part-12 prefix. Its observer
checks all seventeen hash calls, their exact state chain, row-31 framing,
payload pointer/length and both eight-block arrays. A sampler callee cut
checks those arrays and returns arbitrary queries/selected state or an error.
The actual caller forwards the successful query array and selected state;
on error it maps the error to `Transcript` and retains the absorbed state.
Both branches call the sampler exactly once. The trace hook is compiled out
in this library feature configuration, as it is without `prover`; the host
prover's optional trace side effects are not certified by this check.

`transcript-query-caller-v2` passes: exit 0, wall 17.524 s, peak RSS
547220 KiB, zero swaps. The v1 comparison bound 84 is shorter than the
88-byte query array; its unwind failure is retained and replaced by 170.
All safety and unwinding assertions remain enabled. The sampler cut is
explicit, not a verified sampler implementation or a probability law.
It proves the caller transport universally over its outcomes and supplies
the concrete array/result/state boundary for separately composing the
existing sampler proof. It does not replace the whole shared-oracle or
shipped outer execution join.

`ProverCommitScalarPartition.first_accept_partition` proves symbolically
that a sequence bounded by the rejection value has a first success or
exhausts. `sixteen_partition` specializes it to the seventeen scalar cases.
J8369 passes both audits with `[propext, Quot.sound]`: exit 0, wall 1.40 s,
peak RSS 2550616 KiB, zero swaps. No concrete recurrence or large carrier
is reduced. The direct `state_only_hiding::scalar13::mask_scalar_partition` check
subsequently passes: exit 0, 557.458 s, peak RSS 3234648 KiB, zero swaps.
This is one actual shipped scalar execution with no scalar/next-word stub.
Its seventeen-way partition constrains earlier candidates to rejection and
checks the returned value/error, seed, counter (including wraparound),
buffer and word position against a closed-form consumption specification.
The associated Lean lemma establishes exhaustiveness of the cases. The
Debug formatter stub asserts false before divergence, so reaching it would
fail this complete scalar check as well. The counter-indexed oracle table
contains arbitrary answers; it is not fresh independent sampling per word.
The proof has a different shape from the old two-execution timeout and was
not rerun after passing. The corresponding source-scalar run is distinct; its successful nine-way
replacement is recorded below. Whole material-builder transport remains open.

## Stage 4: actual material extraction and demonstrated obstruction

After proving the scalar safety boundary, extraction targets the actual
`build_mask_material_for_layout`, with an intended scalar/balancing call cut. This is a compositional cut, not a change to
the production body. The exact Charon command and all source/tool hashes
are retained. It uses `--release --jobs 4` and a copied, isolated Charon cache.

`material-charon-v1` succeeds: exit 0, 32.189 s, peak RSS 683432 KiB,
zero swaps; LLBC `has_errors=false`, SHA-256
`9c67eeabce7e541c4bb819f96bdb318ec8b33f7375257744195bfac0b3629a0a`,
size 1912945 bytes (binary/intermediate stays on the host).
`material-aeneas-v1` then fails: exit 2, 2.247 s, peak RSS 128832 KiB,
zero swaps. The exact error is:

```text
Unexpected
Source: 'crates/aspis-prover/src/state_only_hiding.rs', lines 471:4-489:1
Compiler source: interp/InterpAbs.ml, line 191
```

The stack reaches `InterpJoin.join_ctxs` / `convert_value_to_abstractions` at
the material-builder loop join. A subsequent LLBC declaration audit finds the
v1 wildcard scalar-opacity pattern did not match: m31/qm31 bodies remained
structured, while the balancing helpers were opaque. Therefore v1 is a
diagnostic failure, not a failure of the intended scalar-cut cone. The v2
command names concrete scalar methods but its declaration audit again finds
the scalar bodies transparent. V2 Charon exits 0 (31.458 s, 652464 KiB,
zero swaps) and Aeneas exits 2 (2.148 s, 128128 KiB, zero swaps), at the same
join. V1 and v2 are retained as configuration diagnostics, not successful
scalar-cut certificates. Each changes the extraction configuration. It is not a Lean
counterexample, a memory failure, or a certificate of the outer caller.
No resource cap is raised; no unchanged translation is rerun.
V3 uses module-level opacity, explicitly re-enabling the actual builder and
record/enum/trait types. Thus helper callees, including constructors, scalar
methods, seed derivation and balancing, are deliberate cuts. A mandatory
post-Charon preflight confirms the actual builder body is structured while
m31, qm31 and both balance helpers are `Opaque`. No Aeneas run is allowed
until that check passes. Charon v3 exits 0: 29.739 s, 691896 KiB, cgroup peak
1117519872 bytes, zero swaps. Its error-free LLBC SHA-256 is
`fb08b05db102c1ddaea77eb438c697ed5cb270a5d81c781fcb0a03fc805a6cfa`,
size 1471036 bytes. Aeneas v3 still fails at the same 471–489 join: exit 2,
1.879 s, 134816 KiB, cgroup peak 119947264 bytes, zero swaps.
This is the confirmed source obstruction after the preflighted callee cut.

The replacement deliverable is an owned, indexed material-loop reference,
with per-iteration Kani equality for the shipped iterator/`?`/Vec update and
Lean induction over that reference, then composition with the accepted
scalar/window and balancing laws. Failed extraction is explicitly excluded.

## Stage 5: source/D boundaries and focused replacement gates

`state_only_entropy::seeds13::d_seed_before_first_scalar` executes the actual
`derive_pool_v1_zero_factor_d` through validation, pool binding and inline D
seed derivation. Its observer checks both complete hash frames with arbitrary
answers. The first-scalar cut checks the exact D seed, zero counter/buffer,
and word 8, then returns `MaskSampleExhausted`; the caller propagates that
error after exactly two hash calls and one scalar call. It proves this prefix
and error propagation, not the successful 1024-element D schedule.
`d-seed-caller-v1` passes: exit 0, 15.344 s, peak RSS 692116 KiB,
cgroup peak 722509824 bytes, zero swaps.

The combined source-seed wrapper is not adopted. Its v1 generic stub syntax
fails before verification (`&mut N` versus `&mut impl StateOnlyMaskNonceStore`),
fixed literally in v2. V2 reaches the 600-second gate (exit 124, 600.002 s,
cgroup peak 3748016128 bytes, zero swaps). The reported GNU-time peak 15832
KiB is the surviving parent, not the already-killed verifier child's peak;
the cgroup peak is authoritative. Four new branch targets replace it rather
than rerunning the combined query. `source-seed-nonce-rejected-v3` passes
(exit 0, 10.751 s, 675100 KiB, cgroup peak 682803200 bytes, zero swaps);
`source-seed-material-error-v3` passes (exit 0, 12.512 s, 675432 KiB,
cgroup peak 682377216 bytes, zero swaps). Both check no source-seed hash is
performed and the actual caller returns an error. The success branch still
reaches the 600-second gate (exit 124, 600.003 s, cgroup peak 3646308352 bytes,
zero swaps; surviving-parent GNU peak 15840 KiB). It remains excluded. The
unconsumed-material branch also reaches the 600-second gate: exit 124,
600.003 s, cgroup peak 3554189312 bytes, zero swaps (surviving-parent GNU
peak 15836 KiB). It is excluded. These failures are bounded-proof/tool
obstructions, not counterexamples or memory kills.

`state_only_entropy::seeds13::source_inline_prefix` separately checks the
literal inline source-seed expression, after an explicit material-success/
consumed boundary cut, with arbitrary entropy and exact context/binding.
It passes: exit 0, 8.247 s, 627416 KiB, cgroup peak 645009408 bytes,
zero swaps. This closes only its local byte frame and returned seed, and
does not certify that the complete successful wrapper reaches that point. No combined or success check is rerun unchanged.

The combined source scalar also reaches the 600-second gate (exit 124,
600.002 s, cgroup peak 3475746816 bytes, zero swaps; parent GNU peak
16008 KiB). It is replaced
by nine distinct fixed buffered-word positions (0..8), with no larger cap and
the symbolic first-success partition retained. The first replacement,
`source-word8-v2`, passes (exit 0, 112.965 s, 1498564 KiB, zero swaps).
All nine replacements now pass. Each uses the actual complete source scalar
with the Debug formatter fail-then-diverge stub and no scalar/next-word stub.
The symbolic first-acceptance partition is retained in every case. The
fixed-position split changes the proof formulation, not the source scalar.

| Exact `state_only_entropy::scalar13::source_word_` suffix | Exit | Wall s | Peak RSS KiB | Cgroup peak bytes | Swap |
|---|---:|---:|---:|---:|---:|
| `0` | 0 | 97.982 | 1412688 | 1536958464 | 0 |
| `1` | 0 | 113.874 | 1510376 | 1635717120 | 0 |
| `2` | 0 | 109.997 | 1478004 | 1604194304 | 0 |
| `3` | 0 | 114.925 | 1501804 | 1627938816 | 0 |
| `4` | 0 | 106.214 | 1481412 | 1607262208 | 0 |
| `5` | 0 | 107.533 | 1498852 | 1625124864 | 0 |
| `6` | 0 | 104.139 | 1503852 | 1630748672 | 0 |
| `7` | 0 | 117.983 | 1481284 | 1607213056 | 0 |
| `8` | 0 | 112.965 | 1498564 | 1624870912 | 0 |

`masked_partition` removes the mathematical candidate-bound premise using
`Nat.and_le_right`; J8370 passes all three audits with `[propext, Quot.sound]`:
exit 0, 1.60 s, 2559336 KiB, zero swaps. `word_partition` proves the nine
legal starting positions exhaustive; J8371 passes all four partition audits
with `[propext, Quot.sound]`: exit 0, 1.42 s, 2566436 KiB, zero swaps.
Together these make the case split exhaustive. Both mask and source scalar
return/state laws are now certified on the stated callback domain. Actual
outer collection, global-window instance and full callback-history transport
remain separate obligations; the abstract Lean step law is not silently
instantiated by naming these certificates.

## Additional outer-prefix family check

`transcript::outer13::public_digest_and_binding_prefix` uses the literal two
secure-API statements between public serialization and
`prove_masked_with_attempt`. Only `attempt.mask_nonce()` is replaced with
an arbitrary nonce argument, making this an explicit source prefix cut.
The observer checks the public-digest call's exact byte slice, the outer
private-attempt domain, same public slice, actual S2 tag and complete encoded
context. It checks both arbitrary returned digests and retained context
fields, with exactly two calls. `outer-binding-prefix-v1` passes: exit 0,
5.079 s, 390188 KiB, cgroup peak 350265344 bytes, zero swaps.
This has a public-byte-length bound 4096; the concrete serializer bound and
public-field image must still be instantiated. No whole secure API or
adaptive shared-oracle theorem follows from this cut alone.

## All-family coverage and remaining obligations

`callback-coverage.json` retains all eighteen families and their source pins.
It marks both complete scalar domains checked, plus local outer, source and D
seed frames and the full query-caller cut. It expressly leaves actual packing,
material/D collection, salts/tree traversal, retries/aborts and global adaptive
execution coupling open. Part 12's accepted row-25 capacity evidence is reused:
its 3751-byte semantic hash input exceeds the old four-point, 514-byte ROM.
No unchanged capacity regression or frozen ELF build is repeated. Arbitrary
response-trace observers cover consistent deterministic traces as a subclass;
they do not assert fresh independent answers or a joint probability law.

The only deleted premise is `builder_premises` on the explicit canonical
specialization. The original arbitrary-input endpoint is byte-identical to
baseline. Both real/ideal execution joins remain literally unchanged. Source
identification and `RustRuntimeJoin` remain peer-owned; no inhabitant is
manufactured here. The next concrete deliverable is the owned indexed material
loop/P6 iteration join, including successful returned-material handling, then
its actual global-window/packing/tree/retry trace composition. The Aeneas v3
failure and successful-wrapper/disposal gates demonstrate why those joins
cannot yet be deleted.

No production Rust/Cargo/program source, frozen ELF input, wallet or account
key is changed. No peer-owned file is edited. Only proof snapshots, text
receipts, source/tool hashes and Lean proof files are committed. Host caches
and keys are retained. No push or merge is performed.

## Final frozen audit and evidence

Preflight checks all twenty adopted Kani receipts, exact source identities,
full 550-file Rust/Cargo input snapshot, required caps/link flags, no swaps,
the deletion-only signature change and the accepted axiom whitelist.
The old local-ROM capacity result, predecessor Lean cache and unchanged
frozen artifact evidence are reused; no adversarial/runtime/SBF suite is
rerun for these proof-only changes.

The single final replay is **J8372**, exact target
**R1Z.ProverCommit13Audit**, importing the part-12 audit and both new adopted
Lean modules. It exits **0**, wall **1.86 s**, peak RSS **4113608 KiB**,
**zero swaps**. Source revision recorded for this audit is **1ab71742c** plus
the literal additive audit/changed partition sources pinned in the receipts.
The dependency fingerprint records the pinned objects used. All **six**
printed public theorem audits use only `propext`, `Classical.choice`,
`Quot.sound`; focused checks also audit the new private caller application.
The scalar partition theorems use only `[propext, Quot.sound]`.
This is one replay of the adopted cached closure, not a new coherent frozen
Rust-to-security release rebuild. Failed translations and timed-out gates
are excluded; no Formatter-dependent Lean theorem is adopted.

`manifest.json`, `validation.json`, `lean/attempts-*.jsonl` and individual
receipts record exact targets, statuses, wall times, peak RSS/cgroup memory,
swaps, source/tool pins, dependency fingerprints and full axiom output.
No new cryptographic assumption is added and no unproved source law is
hidden in a structure. **Target not yet established** for the shipped outer
privacy experiment. Env J attempts are consumed through **8372**; next
available **8373**. No worker process is left running on this job.

## Complete specialized before/after (verbatim)

Only the builder binder is deleted between these two versions. The fixed
input and proved builder contract are defined above both versions in
`ProverCommitAdmittedEndpoint.lean`. The earlier arbitrary-input endpoint
is unchanged and has the part-12 counterexample.

Before:

```lean
theorem privacy_headline_admitted
    (builder_premises : BuilderPremises h B x)
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : (source).Adversary) (w : (R0Z.ZkStatement.HonestProver.Instance h)),
      (R0Z.ZkStatement.HonestProver.public h w) = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 eight_pos
          (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : (source).Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x))
      (idealTestS (fsR1P (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100 := by
  exact PrivacyR1HeadlineOwnedClosed.privacy_headline_owned_closed template input outputs x
    builder_premises observer_program
    R_wire_builder_checker_D75_retry G_sim_R_wire

```

After:

```lean
theorem privacy_headline_admitted
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : (source).Adversary) (w : (R0Z.ZkStatement.HonestProver.Instance h)),
      (R0Z.ZkStatement.HonestProver.public h w) = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 eight_pos
          (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : (source).Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x))
      (idealTestS (fsR1P (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100 := by
  exact PrivacyR1HeadlineOwnedClosed.privacy_headline_owned_closed template input outputs x
    builder_premises observer_program
    R_wire_builder_checker_D75_retry G_sim_R_wire

```
