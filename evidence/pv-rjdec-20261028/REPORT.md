# Decoder and native helper resume — D417

**Target not yet established. Whole ledger rows removed: 0.**

Worktree exactly `/Users/dominic/ZK/.worktrees/pv-rjdec`, branch
`codex/pv-rjdec-20261028`, resume entry `b31649ce7ff391eb76d97011525bf97de2a26d48`.
The preceding report and original receipts remain in `REPORT-before-D417.md`.
All newly created Lean source modules use `R1Z.PV_RJDec_`. Existing RunJoin
sources were neither edited nor rebuilt with changes. No shipped Rust, other
worktree, wallet, account key, endpoint, observer or simulator was changed.

## Restored V221/V222 law actually consumed

The prior source/LLVM diagnostic remains valid about its original model, but
**its compiler-fence mismatch is no longer a stop for this work**. The merged
`PV_RDCD_ZeroWorld`, `ZeroSelected`, `ZeroConsumed`, `ZeroDrop`, `ZeroTrace` and
`ZeroCompatibility` sources were read, pinned at this branch's HEAD and built
privately against the verified inherited cohort. Their original row records
say RESTORED, class C, structural (K-1 substitute), not whole-native-runtime
or privacy closure.

Before, each byte step was `volatileWrite(address, 0); compilerFence(SeqCst)`.
After, each byte step is `volatileWrite(address, 0); asmReadBarrier(address)`:
zeroize 1.9.0's explicit volatile write followed by its x86_64 readonly inline
assembly optimization barrier. `PV_RDCD_ZeroWorld.source_reference` proves
`native (base+i) n w = indexed base i n w`; `ZeroConsumed.emitted_execution`
passes both the complete zero value and that indexed post-world to any Result
continuation. `ZeroDrop.complete` consumes the byte array and returns Unit and
that post-world. Exact ordered history, overwrite, outside-memory/frame and
allocator counter laws are retained. No hardware-fence equality is asserted.

The restored selector installs op122/op123, not op130. The reached
`PV_W_R_ReserveBuild` thunk is precisely op130, `Zeroizing.zeroize`, with the
32-byte emitted dictionary. The deployed 1.9.0 wrapper's complete body is
`self.0.zeroize();`, exactly one delegation. `wrapper-source-binding.json`
retains its source hash and rejects omitted, duplicated and extra-call
controls. Its primitive byte semantics are the restored V221/V222 law; this
is not a new native differential or a compiler proof.

PROVED lower association: `PV_RJDec_ZeroizingSelected.wrapper` installs that
one delegate and proves its complete Result is `.ok (Array.repeat N 0#u8)`.
`PV_RJDec_ReachedZero.complete` identifies the exact reached 32-byte thunk's
outcome with the typed handler and commits the restored indexed post-world,
retaining `[(w,none)]`. `PV_RJDec_AsmBind.complete` keeps arbitrary subsequent
success, failure or divergence, post-world and ordered calls.

`PV_RJDec_ReserveBuild.erase_program`, `MaskedWithAttempt.erase_program`,
`Entry.erase_program` and `Runtime.source` propagate the typed zero-array call
through the actual reified prover caller tree. Their complete source Result
equalities use the explicit selected dictionary. Every other source branch,
error and continuation stays present. This is new reference reification,
not a modification of Rust or the original `PV_W_` / `PV_RunJoin_` programs.

## (a) Both native ROMView laws — OPEN

Neither law has been supplied to `CommonSample32.complete_view` or
`CommonObserver32.complete_pair`. Their exact unchanged all-Result obligations
are, for every adversary, statement and outer Result `out`:

```text
a.disclosed adv x out = b.disclosed adv x (mapR (fun p => (p.1, project p.2)) out)
a.observerOracle adv x out =
  b.observerOracle adv x (mapR (fun p => (p.1, project p.2)) out)
```

`PV_RunJoin_Deployed.Runtime` still takes both fields as arbitrary data. No
native implementation/installation of either field is established here.
Their complete-observation factorization also remains unproved: source
failure and divergence erase post-world and calls in the Result-only carrier;
even success omits the call prefix. The original `Factor.exists_iff`,
`ResultCases.fibres_iff` and pair criterion name the necessary reachable-run
facts. In addition, Common's hypotheses quantify over **all** Results, so a
reachable-run factorization alone does not prove its fixed decoders' total
extension laws. No rejected suffix, failure signal, oracle event, divergence
prefix or side-channel observation has been discarded to obtain equality.

New lower parser work is recorded in `parser-reification.json`,
`recursive-parsers.json` and `chunked-parsers.json`. These reify pinned EJR
**emitted input parser/validator bodies**, preserving every original length,
header, transition, canonicality, binding and validation branch, both Result
layers, outer failure and divergence. They support input identification and
rejection-path work; they are not native ROMView decoders or proof-publication
serialization laws. Native primitive/helper adequacy remains explicit.

PROVED lower complete source laws: `PV_RJDec_ParserR20.source` is
`erase ops (program bytes) = decode_pool_v1_pair_forest_terminal_statement_v1 bytes`
for every byte slice and dictionary, and `PV_RJDec_ParserR12.source` is the
corresponding complete live-snapshot decoder equation. `ParserR15.source`
identifies the complete verified-afterstate decoder. The 15 spliced caller
modules and the named continuation chunks retain their exact source errors.
The final accepted parser inventory and full statements are in the resume
audits and receipts. The unchunked snapshot candidate failed on default
recursion depth; named digest-continuation chunks replace it. No proof limit
was raised and no unchanged failure was rerun. Staged/uncompiled candidates
are explicitly excluded in `resume-uncredited-sources.json`.

## (b) Installed native helper effects — OPEN

PROVED interpreter construction: `PV_RJDec_MemoryInstalled.array_complete`
returns the selected emitted op130 result, the committed
`PV_RDCD_ZeroWorld.indexed` post-world and exactly `[(w,none)]`.
`MemoryInstalled.reserve` and `.drop` retain the previously checked complete
reserve/drop interpreters; `.base_unchanged` preserves the original base
helper/file handler algebra. `PV_RJDec_Runtime.executes` gives the complete
operational execution judgment for the reified entry with this installation.
No world or prefix is removed on a rejected or divergent continuation.

The actual native memory metadata, addresses, view/commit maps, allocation
and free semantics, remaining base helper routing and OS/Drop/unwind effects
are not identified by those construction theorems. The original interpreter's
op130 is still an opaque base helper. The new reification gives that reached
call an explicit typed handler and proves its source Result association;
full native routing/effect equivalence to the original runtime remains P.
No native purity, heap identification, OS silence or assembly/compiler-fence
identity was added as an assumption or trust field.

## (c) Parked V047 native handle/decoder identification — OPEN

The original exact mathematical theorem remains
`AspisR1.PV_2TNV_HeadlineFibre.fibre handle`:
`∃ w : H.Instance, H.public w = (PV_2TNV_PublicEncoding.x handle).1`, where
`H := PhaseWireLog2Bin.honest PrivacyR1HeadlineDeployedReal.input`.
It constructs the transfer-13 witness; runjoin's index-zero fixture does not
match it. The native handle and actual statement equality remain unproved.

PROVED exact transport consumer: `R1Z.PV_RJDec_V047.consume encoded actual
fibre native_identification`, with premises
`fibre : ∃ w : H.Instance, H.public w = encoded.1` and
`native_identification : actual = encoded`, concludes
`∃ w : H.Instance, H.public w = actual.1`.
Instantiate `encoded := PV_2TNV_PublicEncoding.x native_handle` and pass the
original `HeadlineFibre.fibre native_handle`. The missing premise is still
the **actual** native statement/handle/decoder identification, not a ROMView
equality. The consumer proves no native handle construction or wrapper run.
The explicit `FixturePdaRuntime base` and joint proof binders remain required
by the parked joint implication; they were not discharged or added to T.

An additional direct-import cohort gap is recorded in `v047-source-gap.json`:
`PV_2TNV_ByteEncoding` imports `JHb_DataRequest`, whose historical pinned source
is absent at this merged HEAD. It was read through its exact committed pin;
no replacement source or object was invented. That gap is distinct from the
substantive native identification obligation.

## Endpoint and deployment boundaries

Premises removed/added/weakened/changed: **0/0/0/0**. V038, V045, V163, V165,
V167 and V244 remain. All eight `PV_RunJoin_Premises` fields and the exact
three TrustItems (`entropy_law`, `entropy_kernel`, `observation`) are retained.
The coupling, bad/query events, failure-independence requirement and complete
observer/simulator are unchanged. `endpoint-boundaries-unchanged.json` and
`stage-A-source-identity.json` record exact before/after source checks.
Historical three-ELF evidence is reused only for the empty frozen Rust/client
diff from 82566acdfb. Compiler-cohort, D188, K-1/K-2 and L1/L2/L3 boundaries
retain their prior scope. No native correspondence is inferred from finite
validation, source reification or a cached axioms audit.

## Validation and final accounting

All three new audits passed at source revision
`457849e4a8c117b5637f5a3145cc3a78af0abdf5`. No Lean source changed afterward.
The original reserved audit IDs 61397–61399 had already launched before this
resume; the last three unused IDs 61394–61396 were used instead.

| ID | Exact target (`R1Z.PV_RJDec_…`) | Exit | Scope wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| 61394 | ResumeStatements | 0 | 1.79 | 4422848512 | 0 |
| 61395 | ResumeAxioms | 0 | 1.84 | 4419338240 | 0 |
| 61396 | ResumeReplay | 0 | 1.74 | 4419067904 | 0 |

`61394-00.out` prints the complete consumed laws, Common obligations and
world/runtime structures. `61395-00.out` performs 120 combined axiom prints;
`61396-00.out` is the final focused cached replay. All printed axiom sets are
subsets of propext, Classical.choice, Quot.sound. These are focused source
and statement audits, not a frozen release-closure or full-manifest replay.

**Resume tally: 85 Lean attempts, 79 accepted / 6 rejected; 0 new native
scopes; 0 Kani. Job total: 98 Lean attempts, 89 accepted / 9 rejected; 2 earlier
native scopes; 0 Kani; 0 VOID attempts.** All 100 allowed IDs have actually
launched: 98 Lean plus native 61307 and 61311. Thus the numeric remaining
Lean budget of 87 could only fit **85** further launches in the permitted
ID range. No ID was reused or taken outside 61300–61399. **Stop: assigned
ID range exhausted**, not renewed reliance on the old fence mismatch.
The unused native-scope allowance cannot be exercised without another ID.

Every new compiler used one module and one admitted scope, MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000. No cap or prover limit
was raised; no memory kill or timeout occurred. Peak job Lean RSS was
4,422,848,512 bytes; all swap counts were zero. The six new rejected attempts
were 61320 (implicit polymorphic dictionary fields), 61327 (unknown Boolean
simp lemma), 61341 (dictionary rewrite pattern), 61357 (long snapshot
elaboration depth), 61366 (unqualified dictionary type) and 61374 (Result
constructor namespace). Their committed original sources and logs remain;
replacements changed the inputs before compiling again. The long snapshot
case permanently uses named digest-continuation chunks in the generators.

New reservation refusals at 61315 (twice) and 61316 happened before compilers
started. Full 180-second cooldowns were observed, and those still-unlaunched
IDs were retained. Local early retries returned 77 without admission or a
scope. Every actual launch checked allowed:true and admission exit zero in
the same shell command as systemd-run, as required by ruling (t). No refusal
or cooldown launch is credited. Local script/staging corrections are recorded
separately in `resume-local-input-corrections.json` and cost no attempts.

Initial and final inherited-cache checks verify 2,764 project source/object
pairs, 5,802 recorded import fingerprints, 5,673 external objects and 5,438 IR
companions. Final `resume-current-head-check.json` additionally verifies all
1,982 h5 pins against current HEAD with zero mismatches; this additional
HEAD check was performed at final validation, while the initial preflight
checked the retained frozen pin/object cohort. `resume-own-validation.json`
checks all 89 accepted private source/object pairs and 389 direct import
fingerprints. `resume-generator-identity.json` checks all 62 generated Lean
outputs byte-for-byte without writing any source. No accepted object or
source in another job's directory was overwritten.

`resume-validation.json`, `resume-source-validation.json`,
`resume-failed-sources.json`, `resume-original-logs.json`, every receipt,
module record and original output/time pair carry exact targets, source
revisions/blobs/hashes, dependency fingerprints, exit status, wall time,
peak RSS, swap and axiom lines. `resume-uncredited-sources.json` excludes the
failed raw Parser12 and uncompiled raw Parser15, WorldAdequacy and
ParserInterpret drafts. The checked ParserR12/ParserR15 replacements are
credited independently. No uncompiled draft is imported by a final audit.

No native scope, Kani run, extraction, ELF rebuild or unchanged full regression
was added in this resume. Restored V221/V222 evidence is consumed in its exact
structural source scope; its machine, provenance and side-channel boundaries
are not broadened. The wrapper source hash matches the corrected deployed
resolution's 61311 source hash. The private verified cache is retained for
follow-up reuse; no key/account file was touched.

## Next concrete deliverable

Identify the actual native implementations/installations of both Runtime
observation fields, then prove their full failure/divergence-prefix fibres
and their total Result extension laws before supplying Common's hypotheses.
Associate native heap metadata, view/commit, allocator/free and remaining
base-helper/OS/Drop effects with the installed interpreter, including the
routing equality for the original op130 thunk. For V047, prove the actual
native statement equals `PV_2TNV_PublicEncoding.x native_handle` and apply
`PV_RJDec_V047.consume` with `HeadlineFibre.fibre native_handle`, retaining the
explicit fixture-runtime and joint-proof binders in the parked implication.

The exact commit list since resume entry is in `resume-commits.txt`; the final
evidence-freeze commit follows its generation. All three requested native
items remain OPEN; the source and interpreter theorems above are the proved
lower results. No endpoint premise or whole ledger row was removed.
