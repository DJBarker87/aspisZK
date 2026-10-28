# Runjoin38 — source interpolation, serialization and effect-runtime construction

Worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, entry `c9c892ffc073dcae6387cb9ac23b59deaf91abb5`.
The privacy target is not established. **Whole rows removed: 0.** No endpoint
premise was removed, added, weakened or changed. This run exhausted the authorized
100 Lean attempts; the requested full runtime/decoder/security composition is
not complete.

The inherited instructions and runjoin37 report were read. No historical
SelectedMaskProbe/Oracle55 cone was imported, regenerated or substituted. V244's
closure remains the batch-3/pv-b3p6 work; this run did not duplicate its terminal
arithmetic or change crates. No merge, push, shared-cache mutation, key/account
operation or shipped-code edit occurred.

**Checked independent body work.** All new proof files are under
`docs/research/v8-r0-zk-20261009/lean/R1Z/`, with prefix `PV_RunJoin_` and suffix
`38.lean`. Their exact source/object/import pins and results are in
`modules-*.json` and `receipt-*.json`.

* `BasisCell38`, `BasisLoop38`, `BasisExtend38`, `InterpolationCounters38`,
  `BasisFactors38` and `BasisInitial38` associate the actual emitted usize
  descending updates and omitted-node factor recurrence with the retained
  release recurrence. All bounds and counter casts are discharged. The full
  emitted basis helper returns canonical coefficients and a canonical,
  **proved nonzero** denominator. No concrete 28-factor denominator is reduced.
* `ScalarSource38` closes the actual scalar call on arbitrary raw source
  operands. `AccStep38`, `AccLoop38` and `AccPolynomial38` prove every output
  update and its independent polynomial image. `InterpolationRow38`,
  `InterpolationLoop38` and `InterpolationComplete38.interpolate` then prove
  the **entire current emitted interpolator's Result** is successful, canonical,
  and has the 28-node Lagrange polynomial image. No interpolation-success,
  terminal, worker, or desired polynomial equation is assumed.
* `InterpolationPipeline38.complete` composes that result with the actual
  polynomial encoder. `SamplePipeline38.complete` additionally supplies the
  checked actual-round merge: each model interpolation value is the
  quotient-filtered sum of the supplied worker-evaluation cells. Canonicality
  of those supplied cells is explicit. Their association with actual oracle
  evaluations and native worker order/effects is still required.
* `RoundThread38.thread` proves the complete emitted recursive round owner
  equals a finite ordered source fold, preserving both Result layers and
  threading each returned transcript/output into the next round.
  `SumcheckThread38.source` supplies its actual zero-point initialization and
  all ten rounds. The fold retains the actual source round helper and final
  supplied OracleInst comparison: this is source control correspondence,
  **not** the missing independent security-model round equation.

**Checked serialization.** `PolyCell38` preserves the source's raw-limb
normalization; it does not incorrectly identify arbitrary raw inputs with their
unnormalized embedding. `PolyStep38`, `PolyLoop38`, `PolyComplete38.encode` prove
all 28 coefficients are serialized in order into exactly **896 bytes**.
`WideStep38`, `WideLoop38`, `WideComplete38.encode` prove the complete actual
`prover.encoded_slice` Result, all eight limbs per cell and the exact ordered
payload/length, on the explicit backend vector-capacity domain. These apply to
wide-cell slices used by commitments/openings. Native allocation/copy effects
are separate. Complete commitment/opening construction, compact codecs,
query/node serialization and the final published-proof/security-model byte
comparison are **not finished**.

**Effect-runtime construction, with limits.** `RuntimeMemory38.algebra` installs
PV_W/PV_FXM reservation, drop and volatile-zero operations into the reached
prover algebra. Each invocation consults its current-world metadata and commits
the returned buffer/header; it does not capture initialization-time capacity.
`RuntimeMemorySource38` proves all four selected source outcome equations at
that current world and explicitly leaves op227 unchanged. Runtime data still
include native header/address associations, allocator/free behavior, world
views/commits and the base helper/file interpreter.

`RuntimeHash38.source` reifies the original hash callback without changing its
source Result. `RuntimeBody38.source` identifies the recursively spliced actual
S2 entry with the full emitted `prove_masked_attempt`, on the original supplied
public, compilation, hash, attempt secret and store. `initialized_executes`
runs that program on RuntimeInit35's full initialized world. `RuntimeFault38`
embeds extraction errors in the OS-fault carrier without losing the post-world
or ordered call prefix, including on failure/divergence.

This is a checked source construction with explicit runtime data, **not a
concrete native handler installation or a completed `PV_RunJoin_Deployed.Runtime`
instance**. It does not discharge remaining helper/file/OS interpretations,
physical metadata association, native initial-state/store association, or the
joint completion law. In particular neither complete `disclosed` nor
`observerOracle` ROMView decoder law has been proved or supplied to
CommonSample32/CommonObserver32. Their printed statements retain both decoder
obligations. The Result-only Runtime boundary loses post-world data on outer
failure/divergence; its observational adequacy on reachable actual runs must
be proved before the full PV_W Run can be joined there. No failure observation
was silently erased and no observer or simulator was weakened.

**Conditional terminal handoff.** `OracleBridge38.selected_callback` is a named
complete-Result **source-continuation** bridge with a single hypothesis:
`∀ claims, ops.op227 self.public claims point self.challenges =
terminal self.public claims point self.challenges`.
It retains the actual claims, point and retained challenges, public-error
mapping, mask call, eta product and extra column, in source order. It neither
substitutes zero claims nor assumes success of the terminal. The terminal
reference is a data argument; its selected-callback equality is not discharged
or assumed in any credited model/endpoint result. This prepares the callback
replacement, but **does not yet identify the complete SemanticOracle with the
independent security oracle**. The latter requires the remaining claim/mask/
extra and model associations as well as V244's law. No op117 law is promoted to
an op227 law.

**Premises and deployment.** V038, V045, V163, V165, V167 and V244 remain. All
eight existing PV_RunJoin_Premises fields remain; fields removed/added/weakened/
changed: **0/0/0/0**. T remains exactly `entropy_law`, `entropy_kernel`,
`observation`. New runtime data are not new T items or endpoint premises.
The coupling, bad/query events, simulator and complete observer are unchanged.
RustRealRefinement is not instantiated. Native feature/profile/ABI, D188,
allocation, TLS/oracle/filesystem, Drop/unwind and failure-world obligations,
and K-1/K-2 qualifications, retain their prior scope. No new Kani credit exists.

`stage-A-source-identity.json` records an empty diff from 82566acdfb under
crates/, programs/ and tools/r1-cost-probe. Historical stage-A evidence therefore
retains its prior unchanged-source scope; no ELF/client/native differential or
unchanged full regression was repeated. `endpoint-boundaries-unchanged.json`
records the protected endpoint/trust/ledger diff.

**Validation and stop.** Exactly IDs **54400–54499** launched 100 single-module
Lean attempts: **71 accepted, 29 rejected source candidates; 0 Kani**. Accepted
results include 32 new proof/construction modules, three focused audits and 36
newly needed inherited prerequisites. Import/prerequisite validation receives
no theorem-discharge or row-removal credit. Further staged current-body
prerequisites remain listed in `not-compiled-staged-modules.json`.

Each launch required allowed:true and exit 0 admission, then one scope with
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64 and Lean -M7000. A single
vanished-cgroup reservation refusal before 54439 was uncharged; the wrapper
enforced the full 180-second cooldown before admission with that same ID.
No cap was raised, memory kill occurred, or unchanged failed source was rerun.
Three heartbeat-limited factor-proof candidates were replaced by an isolated
symbolic equation and explicitly instantiated rewrite; the accepted factor
proof finished in 2.24 compiler seconds. Their rejected sources and every other
failed candidate are pinned in `retained-failed-sources.json`.

| ID | Audit target (`R1Z.PV_RunJoin_…`) | Exit | Scope wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| 54497 | SourceAudit38 | 0 | 1.84 | 4413083648 | 0 |
| 54498 | RuntimeAudit38 | 0 | 1.80 | 4404994048 | 0 |
| 54499 | BoundaryAudit38 | 0 | 1.89 | 4390281216 | 0 |

Every new theorem prints axioms; accepted sets are subsets of `propext`,
`Classical.choice`, `Quot.sound`. Audit source revisions, commands, exits,
wall/RSS/swap, source authority/blobs/hashes, dependency fingerprints and full
axiom output are retained in receipts and the hash-verified original 100 module
log/time pairs (`original-module-logs.json.xz`). Overall peak RSS was
4468473856 bytes; all swaps zero. These are focused audits, not an endpoint or
complete frozen-manifest release replay.

The initial preflight checked 2319 project pairs and 4876 direct fingerprints.
Final read-only integrity preflight checks **2390 project pairs, 5000 direct
fingerprints, all 5673 external objects and 5438 IR companions**; all match.
Lean is 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, with the same
private env-J/toolchain and LEAN_PATH. No extraction was launched. Exact
environment and absence of own running scopes are recorded in
`toolchain-and-final-scopes.json`. No foreign project object was imported.
Own staging/version-query input errors were corrected before any compiler
started and recorded; no infrastructure repair was attempted.

Stopped on **100-attempt budget exhaustion**, not on a claimed counterexample
or on V244. Next concrete work: instantiate the remaining actual runtime
helper/file/native associations and both complete reachable-run decoders;
finish the worker/oracle and boundary/polynomial/transcript associations through
the source round fold, commitments/openings and whole published serialization;
then apply V244's selected-callback law to the prepared continuation and prove
the independent oracle equation. Only those concrete results can feed the
unchanged CommonSample32/CommonObserver32 and RustRealRefinement composition.

`commits.txt` records the source/evidence commits from entry; an evidence-only
freeze commit follows its generation.
