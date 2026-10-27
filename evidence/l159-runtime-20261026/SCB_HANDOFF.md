# SCB handoff: literal RunView replay obstruction

Branch `codex/cx-l159-runtime-20261026`. **Target not yet established. L159 and
its alias L185 remain open. No SCB_Top.deployed is claimed.** Explicit stop
condition reached; 7/100 Lean invocations, 0/10 Kani. No push or merge.

## Established claim and exact obstruction

`SCB_Replay.annotated_eval` proves that, for the existing `Physical rust`,
if `v = eval H (originalWith rust P)`, the literal annotated result is

    (v.log ++ eval(H, rust(v.input)).log,
      (enrich(build D (view v), v.input), v.accept))

Annotation first records the source execution, then issues the verifier again.
Its second chronological suffix is present even when every read is already
known. Distinct first-read preservation is not equality of chronological logs.
`SCB_Replay.not_single_run` proves inequality when that suffix is nonempty.
This is independent of frozen2/frozen3, model acceptance, query order within
the source, collision worlds and checkpoint bytes.

`SCB_SourceReplay.installed_physical` proves Physical directly for the exact
`DrvC_SourceEntry.source c hashv`, with arbitrary configuration. Its theorem
`installed_single_run` specializes the obstruction to this source, `lift P`
and `canon(lift P)`. Its accepted/nonempty source observations are explicit
conditions, not a claimed fully instantiated deployed fixture.

The first missing sub-obligation is the precise weaker chronological law
`SCB_SourceReplay.ReplayLogLaw rust P runtime`:

    forall H run,
      (eval H runtime).output = some run -> run.accept = true ->
      let v = eval H (originalWith rust (canon P))
      run.log = v.log ++ (eval H (rust v.input)).log

`log_of_binding` derives this necessary clause from literal L159. It is only
the log projection, not a repackaged full carrier/source/security conclusion.
For a faithfully recorded physical view `run = v`, it forces the verifier
suffix to be empty. No approved runtime/game item inserts virtual replay in
the physical log. Adding this equation as runtime trust would contradict any
nonempty accepted single execution. **Do not adopt it as a new runtime law.**

RuntimePersistence still concerns loaded data bytes; the approved game fields
still concern the bank lineage, CP identity/no intervening touch, TX1 parent
status and physical checkpoint actions. None states this virtual log clause.
Even a physical/source observation theorem would not make literal replay
equality follow. The source/experiment association also needs an explicit
relationship between the free account adversary, headline P and runtime;
their existing independent binders do not supply one automatically.

Recommended next deliverable: define the physical execution observation and
prove its annotation/known-cell-replay transport into the headline experiment,
including carried-data enrichment and probability/failure-event transport.
Keep the physical log intact. This changes the endpoint interface and needs
lead coordination with F3X_; no model, contract or other worker file was
changed here. Merely defining an arbitrary runtime to be annotatedWith is not
a deployed binding proof. Proof development stops at this obstruction per the
task's explicit exception to using the whole budget; 93 Lean runs remain unused.

## Before/after, recount and non-vacuity

The actual latest top present in this checkout is `Rc4_Top.deployed`; no Rc5
file was merged. Before/after source statements are byte-identical in
`SCB_BEFORE_Top.lean.txt` / `SCB_AFTER_Top.lean.txt`. The complete kernel
statement is freshly printed in `SCB_007/stdout.log`.

`SCB_LEDGER_DELTA.json` uses the Rc4 ledger method: atomic conjunctive leaves,
one count per quantified law family, shared dictionaries/guards/witnesses,
deployment aliases excluded from independent totals. Offline validation
re-enumerates the retained rows and classes. Actual: **82T/49P/0C -> unchanged**.
Deduplicated deployment-inclusive: **88T/62P/0C -> unchanged**. All retained
audit rows: **88T/65P/0C -> unchanged**. Delta0 everywhere. L159 is one actual
P family; L185 is its alias. No premise/trust item is added, removed or changed.

`SCB_PhysicalRun.countermodel` is a successful nonempty one-query witness to
the mismatch against the exact StoredCarrierBinding definition. It observes
the full physical execution through the actual oracle recorder, whose outer
log and returned view are both computed by `runtime_eval`. It does not assume
an impossible source acceptance. This is an abstract structural model, not
the deployed cryptographic source or a joint fixture of all retained premises.
The existing `CPH_Nonvacuity.joint_runtime` was imported and freshly
axioms-audited with its complete statement; its original fixture limitations
remain. No joint game/installed-crypto/frozen3 inhabitation is asserted here.

## Validation and release boundary

All receipts contain exact target/command, source revision/hash/snapshot,
selected direct object/sidecar fingerprints, exit, wall, peak RSS, swap,
enforced cgroup limits and complete axioms/errors. All13 new theorem audits
and the actual top/CPH witness audit use only propext, Classical.choice and
Quot.sound. Failed recovery sorryAx lines in001/002 are excluded evidence.
006 failed on a missing parser object search path;007 reuses the two existing
Rc4/CPH cache paths. No dependency or infrastructure was built or repaired.

Final audit007: exit0, wall3.071249391s, peakRSS5,356,240KiB, swap0,
source revision8aeeed9dec plus exact dirty audit source hash. Total Lean
wall13.306304840s; same maximum RSS; all swaps0. Every invocation used the
unchanged S2W launchers in coherent SInt2, one module and one scope at a time,
-j1 -M7000 -DElab.async=false, MemoryHigh6G/MemoryMax8G/SwapMax0/TasksMax64.
Every reservation check allowed launch. No retry, timeout, memory kill, cap
increase, package replay or repeated full regression occurred.

`SCB_HOST_SOURCES.json` matches all four SCB sources, direct source imports,
actual top, CPH witness and both unchanged launchers to local bytes. Historical
transitive cache/provenance remains inherited from SInt2, Rc4 and CPH; this is
focused cached verification, not a fresh release closure rebuild.
`SCB_validate.py` and `git diff --check` pass. Final process inspection finds
no remaining SCB Lean process.

Only new SCB modules and this evidence directory changed. No shipped/cfg(kani)
source, other prefix, session A worktree/candidate, key, wallet or funds changed.
No ELF rebuild trigger. Inherited pins, not newly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No binary, object, archive or ELF is committed. Stage commits are local and
plain. The100-bit target remains unestablished.
