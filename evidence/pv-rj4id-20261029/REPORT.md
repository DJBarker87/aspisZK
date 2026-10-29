# Deployed caller identifications — LOG D446

Final focused source/model audit on `codex/pv-rj4id-20261029`, base
`60a288b5461129634a3714d56756a1c64fdca7e4`. No deployed identification or endpoint
premise removal is credited by this report. Sources under crates/ and
programs/ are unchanged. Runjoin's branch/worktree remain read-only.

The native route is `devnet_spend::main` → `plan::run` → `plan::prove` →
`RealR1_client::prove_for_proof_accounts` → `prove_masked_retrying_with` →
`retry_attempt` → `prove_masked_attempt`. It does not instantiate the Lean
Runtime. Exact source pins are in `source-audit.json`; complete checked statements and
original axiom logs are in `64497-00.out`, `64498-00.out` and `64499-00.out`.

## Current item dispositions

(a) **OPEN.** No Rust call constructs the Lean `PV_RunJoin_Deployed.Runtime`,
and no native `disclosed`/`observerOracle` implementation was identified.
`SourceConstructor.runtime`, `LedgerConstructor.runtime` and
`InstalledEndpoint.runtime` forward caller-supplied model functions. The only
explicit native callback at `plan.rs:116` is `|k| accounts.nonce(k)`; it selects
one of eight public account keys and is not an observation decoder. Native
observation includes ordered proof/statement file writes, returned JSON,
`prove_wall_seconds`, errors and the retained side channels. No empty-oracle,
fixed-failure, zero-time or unreachable-result extension was chosen.

The six still-required clauses of `PV_RJDec_CommonCases.complete_pair` are
`disclosed_ok`, `disclosed_fail` (every error), `disclosed_div`, `oracle_ok`,
`oracle_fail` (every error) and `oracle_div`. Its entropy/body/initial-state
hypotheses remain unchanged. Additionally, `PV_RJDec_ResultCases.fibres_iff`
requires equal observations on every reachable successful value/final-world
fibre, every same-error failure fibre and the divergence fibre, including full
query/rejection prefixes. The returned Result erases those prefixes on
failure/divergence. No proof that the actual observer factors through this
carrier exists here; inventing a decoder would not discharge it. No identified
caller-supplied decoder with witness-dependent visible behaviour was found,
so **no checked native privacy counterexample is claimed**.

(b) **OPEN as a deployed identification**, with two checked lower installation
equalities. The exact native calls are `r0::encoder::eval_message` specialized
to WideExact (`prover.rs:354`) and `prover_powers::powers::<29>` (`:360`). Rust
uses static dispatch; the op numbers name modeled foreign entries.

* `R1Z.PV_RJ4ID_Op79.installation [ExternalTypes] (ops : ExternalFuns)` proves
  `PV_RJ4ID_Op79.native ops = PV_DL_EncoderSelected.selected ops`. The left entry
  is `fun inst q p => PV_DL_EncoderNative.value inst q p`; all other fields are
  preserved. `native_control` proves the complete Result equality with
  `PV_DL_EncoderControl.value`, for arbitrary field Result callbacks. This is
  exactly the encoder source installation consumed by ClaimEvaluator48 and
  ClaimEvaluation49. **Native credit remains suspended:** V201's existing
  deployed audit leaves 145 concrete ChunksExact/Zip/array-iterator/index
  records unresolved. Its passing source checker and 1.94.1 finite native
  comparisons do not discharge this own-1 library cone.
* `R1Z.PV_RJ4ID_Op254.entry [ExternalTypes] (ops : ExternalFuns) (N : Usize)
  (x : WideExact)` proves
  `PV_RJ4ID_Op254.callback ops N x = ProverRwP6PowersInstall.powers ops N x`.
  `installation` proves
  `PV_RJ4ID_Op254.incoming ops = {ops with op254 := ProverRwP6PowersInstall.powers ops}`,
  definitionally the input of `PV_RunJoin_GammaPowers44.inputs`.
  `PowersBridge.complete` closes the former carrier/control gap: in
  **ProverRwFull's original carrier**, the indexed source model equals the
  retained early-return source, for every N and arbitrary ZERO/ONE/mul
  callbacks, including fail/div and N=0. Proof uses the decreasing invariant
  `i.val + fuel = N.val`; no concrete recurrence is evaluated. It retains the
  final array writeback and omits the final multiplication. This removes a
  local source-model obligation, not the deployed callback/primitive
  association. RDCD's V261 source-law standing and parametric callback
  qualification are retained unchanged.

Both left-hand incoming dictionaries above are explicit **models**. Neither
is silently called the actual runtime dictionary. The source-to-dictionary
association, effect/primitive association and V370 compiler preservation at
D381/D386 remain P obligations; no assumption was added to T. own-1 requires
statement-by-statement deployed dependency/standard-library binding, including
stores, drop glue, errors and aborts. own-2''' does not apply to these
input-dependent functions or to the complete clock/file-observing client.
Memory primitives are permitted at V370 and allocator influence channels are
classified by the owner's principle; no disqualifying read was hidden inside
an input-free claim. No new extraction, Kani or native result is credited.

(c) **OPEN at the actual caller.** `plan.rs:99` derives the lane snapshot index
from `lane.tree.next_leaf_index`; :107 builds the live terminal statement;
:114 serializes it and :116 passes its semantic public projection. Requests
choose transfer/withdrawal and live records. No concrete request/world/native
handle is bound to the transfer-13 byte record here. This does not prove that
the intended transfer-13 deployment is impossible, and no universal identity
for arbitrary live statements is substituted for the missing concrete one.

`PV_RJ4ID_Statement.required_fields` proves that
`actual = PV_2TNV_PublicEncoding.x native_handle` implies
`actual.1.nextPairIndex = 13 ∧ actual.2 = native_handle`; `other_index` proves
nonidentification for every different index. `consume` applies exactly
`PV_RJDec_V047Native.consume` and supplies its original transfer-13 witness
fibre, but retains the full named equality premise. Thus it is **conditional**,
not closure of V047. Neither this consumer nor the inherited mathematical
fibre executes a joint wrapper. `FixturePdaRuntime base` is not needed by
these mathematical statements; it remains explicit and unproved wherever a
joint wrapper is used. It was not discharged or added to T.

## Premise accounting

Endpoint and whole-ledger-row removals: **0**. Before/after
`PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` and its deployment
conditions are unchanged: removed 0, added 0, weakened 0, changed 0. Local
op254 source-carrier/control equality is newly proved; actual deployment
association remains. E1/E2, V038/V045/V163/V165/V167/V244, complete native
RunJoin, OS-failure independence/rdea-1, V370 and D381/D386, client/public
association, ROM prefixes and L1/L2/L3 remain at their prior scope. T is still
exactly entropy_law, entropy_kernel and observation; simulator and observer
are unchanged. **Privacy target not established.**

## Validation and AGENTS.md section 6 receipts

The combined statement audit **64497**, every-new-theorem axioms audit
**64498**, and the single final focused replay **64499** all passed. These
are focused cached checks, not a frozen-manifest release replay, artifact
fidelity gate or proof of an actual Runtime instance. No unchanged full
regression, Rust/native scope, Kani, extraction, SBF build, push or merge ran.

| ID | Exact target | Exit | Wall s | Peak RSS bytes | Swap | Source revision | Axioms |
|---|---|---:|---:|---:|---:|---|---|
| 64400 | `PV_RJ4ID_PowersControl` | 1 | 2.0 | 4417261568 | 0 | `690b0346b232658f23a050f33eef6741e1728841` | rejected; no credit |
| 64401 | `PV_RJ4ID_PowersControl` | 0 | 2.06 | 4439724032 | 0 | `cfc758ab875c64c6ec67ce551e4aa7c7befc9989` | standard only |
| 64402 | `PV_RJ4ID_PowersBridge` | 0 | 1.97 | 4436275200 | 0 | `690b0346b232658f23a050f33eef6741e1728841` | standard only |
| 64403 | `PV_RJ4ID_Op254` | 0 | 1.92 | 4440608768 | 0 | `690b0346b232658f23a050f33eef6741e1728841` | standard only |
| 64404 | `PV_RJ4ID_Op79` | 1 | 0.09 | 195276800 | 0 | `690b0346b232658f23a050f33eef6741e1728841` | rejected; no credit |
| 64405 | `PV_RJ4ID_Op79` | 0 | 1.31 | 2717265920 | 0 | `690b0346b232658f23a050f33eef6741e1728841` | standard only |
| 64406 | `PV_RJ4ID_Statement` | 1 | 0.52 | 1295011840 | 0 | `690b0346b232658f23a050f33eef6741e1728841` | rejected; no credit |
| 64407 | `PV_RJ4ID_Statement` | 0 | 1.83 | 4594835456 | 0 | `690b0346b232658f23a050f33eef6741e1728841` | standard only |
| 64497 | `PV_RJ4ID_Statements` | 0 | 1.83 | 4677820416 | 0 | `87dfd7e5b001d2bc9196145fd77d135527c0bc38` | standard only |
| 64498 | `PV_RJ4ID_Axioms` | 0 | 1.83 | 4670353408 | 0 | `87dfd7e5b001d2bc9196145fd77d135527c0bc38` | standard only |
| 64499 | `PV_RJ4ID_Replay` | 0 | 2.14 | 4700368896 | 0 | `87dfd7e5b001d2bc9196145fd77d135527c0bc38` | standard only |

The table reports exact per-module wall/RSS/swap measurements, not estimated
resources. Per-scope outer times, complete commands and caps, source SHA256,
Git blob/revision, direct dependency hashes/fingerprints, exits and original
`#print axioms` text are in `receipt-644*.json`, `modules-644*.json`,
`644*-00.out` and `644*-00.time`. All accepted printed sets are subsets of
**{propext, Classical.choice, Quot.sound}**. The rejected 64400 output includes
Lean's unresolved-goal `sorryAx`; it is retained as failed evidence and is in
no accepted final object or audit. Every new theorem, including the combined
replay theorem, has an axiom query.

**Budget used: 11/100 Lean attempts (8 accepted, 3 rejected); 0/30 native
scopes; 0 Kani; 0 VOID; 0 admission refusals.** Only IDs 64400–64407 and
64497–64499 were used. No additional launches will be made from this handoff.
This is an OPEN disposition, not a claim of budget exhaustion or completion
of deployed privacy. The unused budget is not filled with duplicate wrappers
or unchanged gates: the actual observation/statement objects are uninstantiated,
and the new installation equalities do not discharge the explicit deployed
source cone. Every launch checked admission exit 0 **and** `allowed:true` in
the same shell command as its scope, with no cooldown violation. All scopes
used MemoryHigh=6G/MemoryMax=8G/MemorySwapMax=0/TasksMax=64 and Lean -M7000.
Peak over all launches: **4,700,368,896 bytes; swaps 0**. No cap or proof limit
was raised.

Rejected attempts and replacements:

* 64400: `split` could not see through a local pair/let in `dispatch_congr`.
  The source added `dsimp only`; changed source passed as 64401.
* 64404: the older rjdec prefix did not resolve the newer encoder object.
  No source or shared object changed. A private overlay of the h6-verified
  cohort changed this job's import environment; 64405 passed.
* 64406: that private overlay omitted `.olean.server` companions. Original
  companions were hashed and linked beside the same verified objects;
  environment-changed 64407 passed. Neither failure was a memory kill or an
  unchanged rerun. These were this job's own staging inputs, not a host repair.

`h6-result.json` and `source-resolution.json` verify 1,262 transitive project
source/object pairs, every recorded dependency object fingerprint, all 5,673
h4 external objects and 5,438 inherited IR companions, with the original Lean
4.32 toolchain hash `8c9756b28d64dab099da31a4c09229a9e6a2ef35` and inherited
LEAN_PATH prefix unchanged behind this job's fresh overlay. The h4 authority
is the committed rjdec copy of the coherent replay manifest, byte pins checked
against the inherited expectations. EJR's selected joint resolution takes
precedence over same-name union/conventional variants (h5'); this job corrected
its compile-free inventory lookup before any launch. The source read-only
runjoin revision is recorded explicitly in `source-resolution.json` and
`source-audit.json`. No live runjoin branch/worktree or host source/object was
modified. `private-overlay.json` records original companion/object hashes and
symlink destinations inside this job alone. `final-validation.json` rechecks
all accepted new sources, objects and imports and hashes the original logs;
`summary.json` contains complete axiom lines and totals.

The caller also persists/syncs `note-recovery.json`, opens the durable nonce
ledger and performs filesystem/PDA/publication work. These effects are not
removed from the observation obligation. Timing, clock and filesystem effects
prevent treating the complete caller as input-free under own-2'''. No native
counterexample to witness-independent observations is claimed by the absence
of an adapter. This source inspection is not promoted to a source-binding
proof or native experiment result.

No crates/programs file, soundness file, existing PV_RunJoin_/PV_RJDec_/PV_OWN*
source, wallet or account key was changed or removed. No wallet/account was
created or funded. `COMMITS.txt` records `git log --oneline 60a288b546..HEAD`
at evidence freeze; the final report/evidence commit follows its generation.
Every committed evidence file is below 20 MB. Build-host scratch cleanup,
restricted to this job's compiled objects and symlinks, is recorded separately.

## Next concrete deliverable

For (a), construct the actual **effectful observation carrier/adapter** and
prove reachable success, failure and divergence-prefix fibres before fixing
its two total decoders and supplying CommonCases' six clauses. For (b), close
V201's exact deployed 1.94.1 library cone and bind the actual WideExact
primitive dictionary to the now-checked indexed op254 source model; consume
`Op79.installation` and `Op254.installation` without changing their statements.
For (c), pin the intended native request/world/handle, prove its entire public
projection and handle equal transfer-13's byte-derived statement, retaining
FixturePdaRuntime in any wrapper path, then discharge the existing
`PV_RJDec_V047Native.consume` equality premise. Runjoin step (2) was not touched.
