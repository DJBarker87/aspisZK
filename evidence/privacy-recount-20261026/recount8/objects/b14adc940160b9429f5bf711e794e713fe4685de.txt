# Runjoin decoder and native helper audit

**Target not yet established. Whole ledger rows removed: 0.**

Branch `codex/pv-rjdec-20261028`, worktree
`/Users/dominic/ZK/.worktrees/pv-rjdec`, entry
`a9044ce8cd26aeee6cbc1f80d5ade7684c52b882`. All new Lean modules have prefix
`R1Z.PV_RJDec_`. No existing `PV_RunJoin_*` source was edited or rebuilt with
changes. No other branch/worktree, frozen implementation, wallet or key was
modified. No merge or push.

## Disposition of the requested items

**(a) Both complete native ROMView decoder laws: OPEN.** Neither law was
supplied to `PV_RunJoin_CommonSample32.complete_view` or
`PV_RunJoin_CommonObserver32.complete_pair`. Their exact retained obligations
are, for every adversary, statement and complete outer Result:

```text
a.disclosed adv x out = b.disclosed adv x (mapR (fun p => (p.1, project p.2)) out)
a.observerOracle adv x out =
  b.observerOracle adv x (mapR (fun p => (p.1, project p.2)) out)
```

The source provides parameterized runtime constructors, not an identified
native installation of these fields. `RuntimeBody38.initialized` retains its
world and call prefix in a `PV_W_Threading.Run` for all outcomes. The endpoint
decoder input is `Result (Output N L C)`: its fail/div cases retain neither
world nor prefix; even success does not explicitly retain the prefix. No
native reachable-run factorization proof was found or established. No new
complete parser law, canonicality theorem or length-guard theorem is claimed.
Existing parser helpers do not discharge either whole ROMView obligation.

**PROVED, lower interface results:**

* `PV_RJDec_Factor.exists_iff`: for a nonempty observation carrier, a Result
  decoder correct on the given reachable runs exists iff the **entire**
  observation is constant on each fibre of `WorldDecode33.returned`.
* `PV_RJDec_Factor.pair_iff`: that condition on the disclosed/oracle pair is
  equivalent to the condition on each component, without deleting either.
* `PV_RJDec_ResultCases.returned_eq` and `.fibres_iff`: the exhaustive cases
  are equal successful values and final worlds; equal failure errors; or two
  divergences. Each case still needs equality of the full observation.
  Inner parser rejection Results are included in the successful-value case.

These theorems characterize missing obligations; they do not prove them for
deployed execution. No failure, divergence, rejected suffix, oracle event or
side-channel observation was erased to manufacture a decoder equality.

**(b) Installed native helper-effect associations: OPEN.** The current base
helper algebra and Memory metadata/view/commit/free/allocate functions still
lack their full native association. Three complete interpreter-construction
laws were checked:

* `PV_RJDec_MemoryReserve.complete`: the selected op32 outcome, the committed
  complete reference reservation world/buffer, and the call `[(w, none)]`.
  Capacity overflow and allocator refusal remain inner errors with their
  corresponding post-world.
* `PV_RJDec_MemoryDrop.complete`: the selected op4 outcome, reference
  deallocation post-world committed through `dropCommit`, and that call.
* `PV_RJDec_MemoryZero.complete`: the selected op122 outcome, the indexed
  byte-zeroization world committed through `zeroCommit`, and that call.

The statements print all runtime-data parameters. They assert no native
purity, native heap/header identification, OS silence, or generic Drop law.
In particular the reached `Zeroizing.zeroize` call in `PV_W_R_ReserveBuild`
is still a base-helper thunk; giving the separate zeroArray handler a law
does not associate that thunk automatically.

## Checked deployed-body counterexample and stop

The client lockfile `tools/r1-cost-probe/Cargo.lock` selects zeroize **1.9.0**;
the root lockfile selects **1.8.1**. The retained ZeroWorld model records a
`compilerFence` after every volatile byte write. The selected 1.9.0 scalar
body instead calls `optimization_barrier`, whose x86_64 implementation uses
inline assembly with `readonly`, `preserves_flags`, and `nostack`.

The final diagnostic, native scope **61311**, uses rustc **1.94.1**, release
opt-level 3, debug assertions/overflow checks off, and zeroize features
`alloc`, `default`, `zeroize_derive`, exactly as resolved for the deployed
client features `r1p-check,aspis-r1-cost-probe/ct-host-prover`. Every dependency
of the diagnostic is selected at a version in the deployed resolution. The
full client feature graph, source hashes, target and commands are retained.

| Reached helper/control | Volatile stores | LLVM compiler fences | Assembly barriers |
| --- | ---: | ---: | ---: |
| Actual zeroize byte | 1 | 0 | 1 |
| Actual zeroize `[u8; 32]` | 32 | 0 | 32 |
| Old compiler-fence source-form control | 1 | 1 | 0 |

All 256 scalar byte values and 256 uniform 32-byte arrays were tested; both
forms zeroize their values. This is **finite native value validation and a
source/LLVM primitive-schedule diagnostic**, not full Rust semantics, an ELF
rebuild, a native trace-refinement theorem, or a privacy counterexample.

`PV_RJDec_ZeroizeFinding.byte_fence_mismatch` and
`.array32_fence_mismatch` formally show that the model's fence increments
cannot equal the inspected zero-fence diagnostic counts. Those counts are
explicit finite certificate data, not assumed universal native laws.

**Stop:** checked counterexample to a literal association of the inherited
compiler-fence schedule with the deployed helper body. Budgets are unspent;
there was no budget-exhaustion claim. This does not refute every possible
observation-preserving abstraction of the new assembly barrier. Such an
abstraction needs a separate proof, including its effect on the complete
observation; it was not silently equated to a compiler fence here. It blocks
crediting the inherited literal helper schedule as a deployed association.

The first diagnostic (61307) was preliminary: its unrelated proc-macro
dependency unicode-ident initially resolved to 1.0.27. It earned no deployed
credit. The changed dependency resolution pins the client's 1.0.24 in 61311;
the diagnostic source also gained an all-dependency version check. Both
original outputs/locks are retained. No unchanged failed job was retried.

## Parked two-transaction non-vacuity line

The candidate's report and all 31 `lean/PV_2TNV_*.lean` modules were read
through `git show codex/cx-prover-rw-20261023:<path>`. Their pinned revision,
source hashes, imports and declaration inventory are in
`2tnv-source-audit.json`; the exact read-only sources are compressed beside it.

**V047 native handle/decoder identification: OPEN; not supplied by this job.**
The transfer-13 byte-derived public and its mathematical witness remain
distinct from runjoin's index-zero fixture. Neither a ROMView factorization
criterion nor a zeroization effect law identifies the native statement or
commitment handle. Even proved ROMView equality alone would not imply that
input-carrier identification.

The exact checked theorem the V047 witness step can consume **after** that
identification is
`AspisR1.PV_2TNV_HeadlineFibre.fibre (handle)`, whose statement is
`∃ w : H.Instance, H.public w = (PV_2TNV_PublicEncoding.x handle).1`.
Its `public_eq` theorem identifies its constructed witness's mathematical
public. Both accept a handle parameter; neither constructs a native handle.
The missing equality is the actual native statement being
`PV_2TNV_PublicEncoding.x native_handle`, including the native decoder's
public projection. **There is no checked native-identification theorem from
this job to consume for that remainder.** `PV_2TNV_FinalAudit.source_pair`
still supplies byte/data bindings only. Actual same-wrapper TX1/TX2 execution,
the explicit `FixturePdaRuntime base` binder, and the conditional joint proof
remain required. They are not replaced with an honest-acceptance theorem.

## Endpoint and deployment boundaries

Removed/added/weakened/changed endpoint premises: **0/0/0/0**. V038, V045,
V163, V165, V167 and V244 remain. The eight `PV_RunJoin_Premises` fields are
still source_V045, E1_V329, native_fill_V336, native_ledger_V337,
byte_blind_V338, kernels_V339, disclosed_V038 and observerOracle_V038.
TrustItems is still exactly entropy_law, entropy_kernel, observation.

`endpoint-boundaries-unchanged.json` checks the original before/after source
statements, including the Common interfaces and trust/ledger files.
`stage-A-source-identity.json` checks the empty frozen Rust/client diff from
82566acdfb. Historical artifact evidence is reused only in that identical
source scope. The three ELF pins, compiler-cohort boundary, D188, K-1/K-2,
Drop/unwind, native allocation/TLS/filesystem, failure-independence and all
side-channel obligations retain their scope. No existing simulator, observer,
coupling, bad event, query event, failure signal or divergence observation was
weakened. No privacy target is claimed established.

## Validation and receipts

Initial h6 preflight verified 2,764 project source/object pairs, 5,802 direct
dependency fingerprints, all 5,673 h4 external objects and 5,438 IR companions.
Source authority is the inherited EJR/freeze/h5 precedence, with current-HEAD
checks for h5 files. The identical inherited LEAN_PATH prefix and toolchain
were retained after the new private prefix; inherited objects are read-only
links in the new job. Nothing was written into the concurrent runjoin cache.

Every Lean process used one module in one scope: MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000. Native diagnostic
scopes used the same cgroup caps and optimized Rust, -j4. There was at most
one own capped scope at a time. Every launch checked allowed:true and an
exit-zero admission in the **same shell command** as its scope. No attempt
was launched on a refusal or during cooldown; no VOID attempt is claimed.

Rejected Lean inputs, all retained by exact committed source and original logs:

* 61300: first-prefix namespace resolution could not locate the inherited
  WorldDecode33 object. 61301 changes the environment with read-only links to
  the already verified objects; it does not recompile an unchanged dependency.
* 61302: the unannotated Run structure has no generated `Run.ext`. A separate
  explicit extensionality lemma passes as 61303, and changed MemoryReserve
  passes as 61304.
* 61308: the generic Result equality case split left symmetric value/error
  equations. The changed `eq_comm` normalization passes as 61309.

No limits were raised, no memory kill/timeout occurred, and failed elaborations
with sorryAx in their error outputs earn no credit. All **accepted** axiom
prints are subsets of propext, Classical.choice and Quot.sound.

The two 61399 pre-admission refusals started no compiler and consume no ID or
Lean attempt. The wrapper enforced the full 180-second cooldown; a local
early retry exited 77 without contacting admission or launching a scope.
The same ID passed on its third admission after both full cooldowns. Native 61307's
cross-job ID inventory was performed after its launch, unlike the per-Lean
prelaunch inventories; it found no collision. This procedural timing is
recorded, not hidden as a prior check. The corrected native 61311 had a
prelaunch inventory. No ID outside 61300–61399 was used.

Full commands, exact module targets, source revisions/hashes, import-object
fingerprints, exit statuses, wall times, peak RSS, swap and printed axioms
are in `receipt-*.json`, `modules-*.json`, original module `.out`/`.time`
files and the two native receipt directories. These are focused source and
diagnostic results, not a frozen release-closure replay.

The final statement audit, combined axioms audit, focused replay, final
preflight and tally are recorded at the end of this report.

## Next concrete deliverable

Prove the deployed 1.9.0 optimization-barrier effect abstraction, including
the original complete observations, and connect the actually reached
Zeroizing helper thunk to that interpreter. Establish native memory metadata,
view/commit and allocation/free relations and the remaining installed helper
associations. For each disclosed/oracle decoder, prove the reachable-run
factorization conditions printed by `PV_RJDec_ResultCases.fibres_iff`, with
every actual parser rejection/canonicality/length guard and native failure or
divergence prefix. Then supply those laws to the unchanged Common interfaces.
Do not count any row removed before the later endpoint composition.


## Final combined audit and focused replay

All three reserved audits passed, at source revision
`0b5331a8fbfd6ce5facf02325eca83e2c7d25587` (the separately recorded exact source
hashes pin the files). No proof source changed after these audits.

| ID | Exact target (`R1Z.PV_RJDec_…`) | Exit | Scope wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| 61397 | StatementAudit | 0 | 2.48 | 4388405248 | 0 |
| 61398 | AxiomsAudit | 0 | 2.35 | 4387569664 | 0 |
| 61399 | FocusedReplay | 0 | 1.84 | 4401872896 | 0 |

`61397-00.out` prints the full statements, including all runtime parameters
and the Common interface hypotheses. `61398-00.out` combines the mismatch
statements with axioms audits of every new theorem and both Common consumers.
`61399-00.out` is the final focused cached replay. All axiom sets are subsets
of propext, Classical.choice, Quot.sound; `PV_RJDec_Run.ext` and the pair-fibre
law use no axioms. No native property is smuggled in as a new Lean axiom.

**Final tally: 13/100 Lean processes, 10 accepted and 3 rejected; 2/40 native
scopes; 0 Kani; 0 void attempts.** Peak Lean RSS was 4401872896 bytes; all swaps
were zero. The final dependency preflight retains the 2,764 baseline project
pairs and all external/import/IR checks; `final-own-validation.json` additionally
checks all 10 delivered source/object pairs and records zero own running
scopes. The private Lean cache is retained read-only for follow-up reuse.
Only this job's 48,636,490-byte rebuildable native target directory was removed,
after its artifact hashes/sizes were recorded. No key/account file was touched.

`validation.json`, `source-validation.json`, `retained-failed-sources.json`,
`post-preflight.json`, `final-own-validation.json`, native receipts and original
logs carry the detailed evidence. `commits.txt` lists commits since entry;
the final evidence-freeze commit follows its generation. No endpoint premise
or ledger row was removed. Both requested native items and the 2tnv native
identification remainder remain OPEN.
