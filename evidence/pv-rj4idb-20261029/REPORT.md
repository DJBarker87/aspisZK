# Deployed caller observation and source associations — LOG D448

Final focused source/model result. Branch `codex/pv-rj4idb-20261029`, exact sparse worktree
`/Users/dominic/ZK/.worktrees/pv-rj4id`, base candidate `f63ed1bd4e`.
The prior report is preserved unchanged. No crates/programs or runjoin sources
are edited. No pushes, merges, Kani, wallet/key operations or release builds.

## Scope and claim boundaries

The native observation decoder is constructed as a composition of explicit
channels, with a lossless ordered carrier and failure/divergence prefixes.
Native acquisition and old Runtime compatibility are distinguished in
[OPEN-INPUTS.md](OPEN-INPUTS.md). Actual Runtime installation is not inferred
from an abstract decoder or from a Result-only theorem.

The focused targets, corrected combined statement/axioms audit and single
final focused replay are complete. Deployed privacy remains unestablished.

## Final dispositions

**(a) PROVED: explicit decoder construction; OPEN: deployed channel acquisition
and old Runtime installation.** `PV_RJ4IDB.native_factorization` states exactly

```lean
{A : Type} (t : PV_RJ4IDB.NativeTrace A) :
  PV_RJ4IDB.nativeObservation t =
    PV_RJ4IDB.decoder (PV_RJ4IDB.modelTrace t)
```

This is a construction on recorded native channels, not a claim that the
Rust binary has been instrumented or that its execution-to-record association
is proved. The observation retains cross-channel event order; proof and
statement file requests and deliveries; other file creation, recovery-data
write/sync and durable-ledger effects; returned JSON and stdout; both diag2
and diag3 event alphabets; counts, exact serialized wall time; oracle and
rejection prefixes; retained channels and the full terminal. `all_prefixes`
quantifies over **every index of an arbitrary prefix family**, including every
emitting divergent prefix. Panic metadata and abort register/memory payloads
are retained. `diagWithState` additionally retains an explicit final visible
state projector on every exit; private state is not silently declared public.

`actual_factors` gives the corresponding equation on the existing
`PV_W_Threading.Run W Event Error A` carrier. `result_fibres_exact` applies
`PV_RJDec_ResultCases.fibres_iff` and proves the **iff**, not only sufficiency:
full ordered-event prefixes must agree on each same-value/final-world
success fibre, every same-error failure fibre, and the divergence fibre.
`component_cases` supplies this exact three-way statement for each component.
The failure and divergence requirements are not set to empty histories.

For available returned proof/count/status components, `ReturnedOutput`
preserves done/proof/attempts, retry, every verifier stop, every outer failure,
and divergence. `returned_output_fibres` proves their fibres.
`output_disclosed_ok/fail/div` and `output_oracle_ok/fail/div` prove all six
CommonCases-shaped total-extension clauses under unchanged component
consumers. `DecoderCases` gives the six general explicit pullback equations.
These **do not instantiate** the full native Runtime.disclosed or
Runtime.observerOracle. Those still need the nine typed open inputs in
`PV_RJ4IDB_OpenInputs.lean`, listed one per missing component with owning line
in [OPEN-INPUTS.md](OPEN-INPUTS.md). They are uninstantiated Props, not axioms,
new T fields, or premises of a theorem asserting its own conclusion.

The actual source order is checked in `caller-source-map.json`: recovery
write/sync and nonce-store open precede proving; `proof.bin` precedes
`statement.bin`; both precede JSON construction, which precedes main's
stdout print. `ClientSuffix` proves preservation of earlier file prefixes
when later statement I/O fails or JSON construction diverges. Native file,
JSON/formatting and clock executions remain owner inputs.

The unchanged PV_DIAG3 client, ownership, write, formatter, syscall, capture,
reporting and observer models are consumed through new adapters, together
with PV_DIAG2's unit-error spelling and final-Rejected exclusion.
`native_normal_model` composes the source retry leaf with the selected native
continuation; `ClientAbnormal` preserves panic/abort/divergence and final
visible state. `DiagSyswrite` preserves fd2, bounded requests, errno leaves
and abnormal prefixes. `DiagJoint` consumes the **original joint coupling**,
including exposed state, rather than making new simulator coins or combining
marginal count/time laws. The complete honest native leaf/coupling law remains
open. Unit content selection is not an occurrence, capture-PC or delivery law.
No checked same-public native privacy counterexample is claimed.

**(b) PROVED at the own-1 deployed source/complete-Result boundary for op254;
op79 OPEN on the assigned dependency.** The exact consumable equations are:

```lean
R1Z.PV_RJ4IDB_NativePowers.deployed_callback
  [ProverRwFull.ExternalTypes] (ops : ProverRwFull.ExternalFuns)
  (N : Aeneas.Std.Usize) (x : ProverRwDictionaryTower.W) :
  R1Z.PV_RJ4IDB_NativePowers.callback ops N x =
    R1Z.ProverRwP6PowersInstall.powers ops N x

R1Z.PV_RJ4IDB_NativePowers.deployed_installation
  [ProverRwFull.ExternalTypes] (ops : ProverRwFull.ExternalFuns) :
  R1Z.PV_RJ4IDB_NativePowers.installed ops =
    {ops with op254 := R1Z.ProverRwP6PowersInstall.powers ops}
```

The right-hand dictionary is definitionally runjoin's unchanged
`PV_RunJoin_GammaPowers44.inputs ops`. These equations add no callback-law,
canonicality, positive-size, successful-return or desired-equality premise.
`NativeConstants.deployed29_total` covers the actual static N=29 call;
`PowersSafety`/`PowersTotal` prove every model size, N=0 included, all index
bounds, exact increment without wrap, mutable restoration, totality and
absence of source Result failure/divergence under the selected native
primitive interpreter. The original symbolic decreasing invariant is used;
no N=29 recurrence is kernel-normalized.

Unlike the preceding round's model-only installation, `NativePowers` selects
an explicit **deployed CT source interpretation** for multiplication.
`FieldQ`, `FieldR`, `FieldQMul` and `FieldWide` transport its complete Result
through the existing CT/base/complex source bridges to the captured runjoin
primitive. ZERO and ONE are proved from named eight-limb constant equations.
`StdIndex.source_equal` preserves the retained arrayOutOfBounds constructor;
its native panic path is unreachable in the powers loop by the proved bounds.

`op254-source-binding.json` checks complete powers tokens, the exact static
WideExact/N=29 caller, selected feature arms, complete reached arithmetic
bodies and literal constants. It binds each control/store/return step to the
Lean interpretation and retains complete Rust1.94.1 array/slice-index,
conversion and integer-primitive source regions. The only store-order
transport (native store before multiplication versus delayed pure Result
restoration) is justified by selected multiplication totality and full final
writeback. It is **not** an erasure of native store/crash observations.
Recursive Copy records have no user Drop; this leaf has no allocator or
external-state read. Compiler/memory intrinsics remain at V370.

Evidence class: **structural (K-1 substitute)**, with native finite validation.
Rust1.94.1 opt3, overflow/debug assertions off, the original deployed feature
graph/rlibs and exact powers source passed **32,768** same-input pairs,
including N=29, N=0/1/2/255, changed-output restoration, and a negative control.
This is finite validation, not an exhaustive universal native execution proof.
The compiler-preservation obligation **V370 / owner D381/D386** and physical,
OS/crash and whole-RunJoin observation obligations remain explicitly retained.
The local static op254 source/dictionary identification is removed at this
boundary; no whole V165/V167 or privacy-headline premise is removed.

For op79, V201's **145 iterator/index records belong to pv-rdcd3**. This round
records that dependency and does not duplicate it, change its standing, or
claim that the earlier Op79.installation alone closes native deployment.

**(c) PROVED byte-pinned caller-to-transfer-13 equality and V047 fibre;
OPEN at the actual live native record/handle binding.**

```lean
R1Z.PV_RJ4IDB_CallerSemantic.caller_to_transfer13
  {CH : Type} (native_handle : CH) :
  R1Z.PV_RJ4IDB_CallerSemantic.caller native_handle =
    AspisR1.PV_2TNV_PublicEncoding.x native_handle

R1Z.PV_RJ4IDB_CallerSemantic.consume
  {CH : Type} (native_handle : CH) :
  ∃ w : R1Z.PV_RJDec_V047.H.Instance,
    R1Z.PV_RJDec_V047.H.public w =
      (R1Z.PV_RJ4IDB_CallerSemantic.caller native_handle).1
```

There is **no `identified : actual = x native_handle` hypothesis** in these
new equations. Payment fields come from the retained request bytes. The live
index and all twenty frontier digests come from the retained lane bytes,
transported through the existing complete byte-window equalities. The
candidate-afterstate root/frontier comes from transfer-13's retained output.
`CallerSemantic.typed_projection` follows the native transfer semantic-public
field selection; the fibre is obtained by exactly `PV_RJDec_V047Native.consume`.
The unchanged WorldData and account literals were recompiled privately only
because their objects were missing from this job's closure.

The Rust1.94.1 deployed-configuration fixture check decodes the retained
1,880-byte statement and confirms **all 1,455 semantic-public bytes**, index
13 and a changed-index negative control. This is finite fixed-fixture
validation. `caller-source-map.json` checks the real caller and semantic field
selection. It does not establish that an arbitrary live request, actual
compiled afterstate or actual commitment handle is this fixture. Those exact
native producer associations remain open; a universal transfer-13 identity
for arbitrary live statements is neither stated nor used.
`FixturePdaRuntime` is not required by the mathematical projection/fibre and
has not been discharged or added to T. It remains explicit and unproved in
any proposed joint-wrapper path; no joint wrapper was executed here.

## Premise accounting

`endpoint-accounting.json` byte-compares the exact before/after
`PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` source at base
`f63ed1bd4e` and the final proof revision: **removed 0, added 0, weakened 0,
changed 0** headline premises/deployment conditions. The local op254 static
source/dictionary identification is newly supported at the stated own-1
source/Result boundary. No native privacy endpoint closure is inferred.

T remains exactly `entropy_law`, `entropy_kernel`, `observation`. The simulator
and existing observer are unchanged; the new observation carrier/adapters do
not replace them. Native RunJoin, E1/E2, compiler preservation and D381/D386,
complete actual client/public association, OS failure independence/rdea-1,
ROM prefixes and L1/L2/L3 remain at their prior scope. Missing native producer
facts are P obligations, not cryptographic assumptions. **Privacy target not
established.**

## Validation and AGENTS.md section 6 receipts

All **89/89 new Lean attempts** were used: **71 accepted, 18 rejected**. Together
with the prior round's 11 attempts this uses the original 100-attempt allowance.
There were **2/30 capped native scopes**, **0 Kani**, no extraction, SBF/release
rebuild, push, merge or unchanged full regression. The native count is an
upper bound; no unchanged native gate was repeated to fill it.

The exact target, exit, wall time, peak RSS, swap, source revision, source and
dependency fingerprints, and complete original `#print axioms` result for
**every Lean attempt** are in [receipts.md](receipts.md), `summary.json`,
`modules-646*.json`, `receipt-646*.json`, and original `646*-00.out/.time`.
Every accepted printed set is a subset of
**{propext, Classical.choice, Quot.sound}**. All 131 new theorem declarations
and nine typed open-input definitions are covered by the final combined
queries. New theorem count is an audit-coverage check, not premise-removal
credit. Source and exact statements are frozen in `proof-source-freeze.json`.

| Audit | Exact target | Exit | Wall s | Peak RSS bytes | Swap | Source revision |
|---|---|---:|---:|---:|---:|---|
| 64697 | `PV_RJ4IDB_Statements` | 1 | 2.10 | 4683186176 | 0 | `7210769c022df0e77c2fac0a67104cb219c852f8` |
| 64698 | `PV_RJ4IDB_Axioms` — corrected combined statements and all axioms | 0 | 2.24 | 4696432640 | 0 | `5db17285b9ac7a17aea1169a057d808f3cf8859e` |
| 64699 | `PV_RJ4IDB_Replay` — single final focused cached replay | 0 | 1.77 | 4689207296 | 0 | `5db17285b9ac7a17aea1169a057d808f3cf8859e` |

64697 caught a missing **audit-only CommonCases import**; it did not invalidate
the focused proofs. Its exact failed source is retained as
`failed-64697-source.lean.txt`. The corrected full statement queries were
combined with the axioms queries in 64698, preserving the final replay at
64699 and the 89-attempt cap. The rejected Statements module is not imported
by any accepted audit or included in the final accepted manifest.
`make-audits.py --check` reproduces the corrected frozen audit sources.

The per-target Lean wall total is **150.74 s**. Peak across all attempts is
**4,696,432,640 bytes**, swap **0**. Every actual scope had
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Lean used -M7000.
One scope ran at a time. No cap, heartbeat or recursion limit was raised.
Every launch checked admission exit 0 **and** allowed:true in the launching
shell. There were **0 refusals, 0 VOID launches and 0 cooldown violations**.

The separate admitted **64600 scope failed before Lean started** because this
job's fresh offload lacked its runner script. Original exit2/time/RSS logs and
`receipt-64600.json` are retained. The staging environment was corrected;
64601 then compiled the source. 64600 is conservatively retained as a consumed
ID but is **not one of the 89 actual Lean launches**. This was an own-input
staging error, not a shared launcher/host repair. The wrapper's final budget
check counts actual per-module launch records rather than empty scopes.

Native receipts `native-powers-receipt.json` and
`native-statement-receipt.json` record the complete capped commands, source
revision, rustc1.94.1 toolchain, release flags, deployed resolved feature/unit
graph, exact rlib and binary SHA256, input hashes and output. Native powers:
exit0, wall1.69s, peak119779328 bytes, swap0. Native statement: exit0, wall0.25s,
peak126676992 bytes, swap0. `#print axioms` is N/A for those finite native runs.
They are not singleton-domain exhaustive claims under own-2'''; both tests
are explicitly finite validation. No quarantined Kani result is used.

`final-validation.json` checks all **71 final accepted source/object pairs**
(including unchanged newly required diagnostic/fixture prerequisites), every
recorded direct import hash, all new theorem queries, and **1,298 inherited
h6 project objects**, with zero mismatches. Before the first launch the h6
preflight checked source resolution, complete transitive fingerprints, all
5,673 h4 external objects, 5,438 inherited IR companions, Lean githash
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, and the inherited LEAN_PATH prefix.
The final root extension added the already verified current CT and powers
source cones; no external/library object was rebuilt or substituted.
EJR precedence and the user-authorized read-only runjoin ref were retained.

Build-host staging used the fresh private directory
`/home/dombarker/project-offloads/codex-pv-rj4idb-20261029/`, linking the verified
old caches read-only and leaving the previous rj4id staging directory intact.
No runjoin worktree/branch, shared source/object, crates/programs file or
soundness file was changed. No wallet/account key was created, funded,
destroyed or removed. This report does not export recovery data or claim it
unobservable. No compiled object, executable, archive or ELF is committed;
each evidence file is below 20 MB. Own host sources, objects and receipts
remain available for checked downstream reuse.

## Failed attempts and replacements

Every rejected original output is retained and uncredited. None was a memory
kill, timeout or unchanged compiler rerun.

* 64603/04: corrected the implicit-argument use of `List.filterMap_append`.
* 64606/07: used a symbolic list induction for diagnostic recovery.
* 64610/11: fixed native byte namespaces and the local field characteristic.
* 64620/21: applied named complex-carrier round trips in the quartic bridge.
* 64625/26: replaced a reserved Lean parser identifier in the publication law.
* 64629/30/31: disambiguated WideExact/dependent Array.set, then removed a
  no-progress reduction tactic in the totality induction.
* 64632/33: installed the native primitive instance before rewriting powers.
* 64635/36: normalized the channel induction hypothesis before each symbolic
  constructor case; the generator records this permanent proof form.
* 64639/40 and 64673/74: distinguished outer runtime Error from verifier Error.
* 64641/42: transported the little-endian natural through its explicit M cast.
* 64652/53/54: disambiguated dependent Array.set and index notation, then
  corrected the proposed index model's panic tag to the retained
  **arrayOutOfBounds** constructor. The initial all-index equality was false
  at out-of-bounds indices; no credit is assigned to it. The final source
  convention matches, and powers independently proves that branch unreachable.
* 64675/76/77: corrected the global verifier namespace, then removed a tactic
  after a rewrite had already closed the diagnostic suffix goal.
* 64683/84: unfolded named field constant equations, not opaque constants by
  kernel reduction; only the small eight-limb literals are inspected.
* 64697/98: added the missing audit-only import and combined corrected
  statements/axioms. No substantive theorem statement changed.

## Stop and next concrete deliverable

The **89-attempt Lean budget is exhausted**, with the accepted combined audit
and final focused replay complete. This is this job's focused manifest, not a
whole frozen deployed-privacy release replay; no latter claim is made.

Next: the owners supply the nine exact native channel producers and their
full old-Result prefix-fibre laws from `OpenInputs`/`OPEN-INPUTS.md`; runjoin
consumes the unchanged op254 installation equation after its own sequencing
requirements are met; pv-rdcd3 supplies V201's 145-record op79 binding. Bind
CallerSemantic's transfer/lane/output record and handle to the intended live
native caller, with FixturePdaRuntime retained wherever a joint wrapper
enters. Only then can the complete native observation be installed into
CommonCases and a coherent whole-privacy replay be meaningful.

`COMMITS.txt` records `git log --oneline f63ed1bd4e..HEAD` at the evidence
freeze; the final receipt/report commit follows that listing.
