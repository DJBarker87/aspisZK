# Privacy owner decision packet — 2026-10-27 (B)

Target not yet established. Evidence is frozen by the
[recount 8 pins](../evidence/privacy-recount-20261026/recount8/pins.json).
Approvals resolve the named choices; native proof, adoption and release binding
remain separate obligations. D248 already adopted option B and the capped
RunJoin trust list, exactly entropy_law, entropy_kernel and observation.

Client toolchain is **owner-APPROVED**. The security contract's second amendment
of 2026-10-27, item 4, and LOG D301 approve rustc/cargo 1.94.1
(rustc e408947bfd200af42db322daf0fadfe7e26d3bd1, cargo 29ea6fb6a), LLVM 21.1.8,
x86_64-unknown-linux-gnu, recorded RUSTFLAGS and no target-cpu change, as
recommended in D270. The candidate contains
`tools/r1-cost-probe/rust-toolchain.toml` (ff50df39a8). Rustup applies it when
cargo runs inside that client directory; it does not select the root/program
build toolchain. Adoption must re-confirm the pin. This resolves the compiler
selection question and enables an identifiable client build; compiler
preservation and the final binary evidence remain P obligations (V370).
Evidence: LOG D270/D301 and `design/RELEASE-LEDGER-20261025.md`.

D188 narrowing is **owner-APPROVED** by item 3 of the same second amendment
and LOG D301. The raw low_base_p_digits emission loses a mutable restoration
and cannot supply its native source law. Native bridging of the excluded body
and per-function writeback checks remain proof work. Stream A's SDY checks
restore the four overlapping functions' credit on the checked fixtures under
ruling (o)/D302; they do not establish universal adapter or chronological-trace
fidelity. pv-d188 governs the other Stream B emissions: no closed callback is
withdrawn, while unchecked native/effect composition remains suspended.
Evidence: LOG D300–D303, candidate `evidence/pv-d188-20261027/AUDIT.md`, and
research `evidence/fidelity-check1-20261027/SDY_FINDING.md`. This resolves the
contract choice and permits the narrowed association/bridge work; it does not
approve a new translator or add a trust field.

The fifth owner amendment of 2026-10-28 adopts composition-trust option A.
Every use of Kani, Charon or Aeneas agreeing on Rust semantics is
reclassification within existing tool trust, never premise removal. It approves
no additional RunJoin T field. FixturePdaRuntime remains deferred. The standing
delegation is to the soundness lead and preserves privacy; D396 explicitly
keeps the privacy choices below with the owner. No later adoption of those
choices occurs at the recount pins.

The following decisions/actions remain open.

1. **Release recipe and constant-time private-input decoding.** The question is
   whether to adopt ct-host-prover on, insecure-spend-fixture off, a locked build
   with the approved client toolchain, and fixed-width constant-time decoding
   for private input, as recommended in D272/D276. Options are that recorded
   recipe and decoding route, or another explicit recipe/decoder with renewed
   evidence. The fscan deployed client unit graph still includes the transitive insecure-spend-fixture feature; this is the measured current configuration, not adoption of the proposed fixture-off recipe. The historical recipe retains N1; inspected audit B removes N1,
   while N2–N6 remain L2/native obligations. The client toolchain approval does
   not adopt the features or decoder. This unblocks the selected release binary,
   final transitive audit and qualified V374 campaign. Disabling the fixture
   feature does not remove internally constructed fixture notes. Evidence:
   LOG D272/D276/D278/D301, candidate
   `evidence/pv-l3-20261027/dual/AUDIT.md`, and the release ledger. D295's
   nonconforming timing detection was diagnosed as an input-preparation
   artifact in D297; plan v2.2 is prepared, not a completed final V374 pass.

2. **N7 signing-key custody.** The question is whether to adopt the prepared raw
   64-byte keypair pipe and fixed-copy Rust decoder, or retain decimal parsing
   while preparing another measured repair. D272 recommends fixed-width
   private-input decoding; D283/D284 prepare this remedy for review. D284
   classifies N7 as signing-seed custody, not witness privacy. Approval unblocks
   signing-boundary integration and the remaining custody audit. Python
   parsing/storage, OS I/O, validation and signing still need treatment.
   Evidence: LOG D283/D284/D301, candidate `design/PV-N7-20261027.md` and
   `evidence/pv-n7-20261027/patches/0001-private-key-raw-fd.patch`.

3. **SHA-NI trust item versus soft backend.** The question is whether to change
   the trust contract for instruction semantics, prove the SHA-NI refinement
   under the existing cap, or select a soft backend with its timing and adoption
   gates. The current capped T permits no additional instruction field. D273
   records the worker's recommendation to retain SHA-NI and prove refinement;
   it records no separate explicit lead backend selection. The +5.93 s /
   19.6–19.9 s soft estimate is a projection, not a measured whole-prover gate
   failure. A decision unblocks the dispatcher/instruction refinement route
   for V231–V238. V233's split law does not resolve this choice, and its deployed native link is currently suspended. The restored V238 wrapper keeps its finalizer and TRUNC_SIDE parameters; it does not establish V232 instruction semantics. Evidence:
   LOG D263/D273/D301 and candidate `design/PV-SHA-DISPATCH-20261027.md`.

4. **DOITM implementation.** The question is how to implement the already
   adopted DOITM-only acceptance of V371. Options are a firmware/kernel/Secure
   Boot configuration permitting enablement and verification, or retaining
   V371 unresolved while DOITM is off. D248 recommends and records owner
   acceptance only in DOITM mode; Secure Boot lockdown blocks the raw MSR write.
   This action unblocks physical instruction-timing transfer, while the L2
   proof obligations remain. Evidence: LOG D248/D301, the ledger's owner
   decisions, and `codex/pv-l2b-20261027:evidence/pv-l2b-20261027/V371.md`.

5. **Client scope.** The question is whether the release scope is the pinned
   devnet fixture harness or a user wallet accepting witnesses from user notes.
   D284 records no recommendation for either option; D320 retains the question.
   The current client constructs fixture witnesses and is not a wallet.
   D320 establishes the source consequence: the endpoint's Selection.selected
   is caller-supplied; frozen RealR1_client receives public and compiled
   arguments and selects no deployment index, and its source callers are
   fixture tests. No deployment selector occurs in that frozen source. Fixture
   results supply non-vacuity instances. The later honest-family theorem supplies
   V152–V154 on its explicit subtype; V038 common-sample agreement remains open. Choosing scope unblocks a concrete
   client/witness/caller interface and the required execution, custody and
   privacy bindings. Evidence: LOG D284/D301/D320, candidate
   `evidence/pv-n7-20261027/INVENTORY.md`, and pinned runjoin
   `evidence/pv-runjoin21-20261027/STAGE1-SELECTION.md`. The privacy target is
   unchanged.

Extraction beyond Drop is information following D291, rather than a remaining
owner decision. The unchanged pinned extractor accepts representative
Drop-free prover-local rewrites under the existing D187 route; equivalence,
module gates and timing still require evidence. SHA wrappers remain with the
SHA-NI item above. No translator re-pin is approved by this packet.

## Decision: full withdrawals (zero change) and the honest-user domain (LOG D338, 2026-10-27)

**Question.** The admitted spend relation (BuilderSpendRelation.RspendPlus) includes a withdrawal of
a note's entire value with zero change; Lean proves such a spend admitted (PV_RunJoin_SpendDomain27,
attempt 38144). The frozen native wrapper compile_pool_v1_pair_forest_withdrawal_merged_c1_v1
rejects `witness.change.value == 0` with Err(Conservation) before compiling, so the shipped client
cannot prepare it (native probe pv27-zero-change-03; a 250/750 withdrawal succeeds as control).
Evidence: codex/pv-runjoin-20261026, evidence/pv-runjoin27-20261027/FINDING.md and REPORT.md.

**Options.** (A) State the privacy claim's honest-user domain as spends whose preparation succeeds,
which today requires positive change, and record separately that users cannot withdraw a full balance
through the shipped client (they must leave at least one unit as change). No implementation change.
(B) Change the frozen compiler to accept zero change, which reopens the implementation freeze, the
three ELF pins if the change reaches crates/ code compiled into release programs, and the affected
proofs.

**Lead recommendation.** (A) for the privacy claim now, because it changes no implementation and
the zero-change guard rejects locally before any proof or transaction is produced; the functional
limitation goes to the owner as a product question, independent of privacy. CanonicalHonest31 and Coverage31 now prove the source-level coverage for the codec-first route. Actual native caller, world and observation association remains necessary under either option.

**Unblocks.** The exact honest-user domain in the privacy statement; the coverage half of the
honest-family source identification (D337).

**Update (LOG D342, 2026-10-28).** The zero-change rejection is not specific to withdrawals: the
admitted relation also contains a transfer with zero change (400 in, 400 to the recipient, 0 change),
and native preparation rejects it with Err(Conservation) as well (codex/pv-runjoin-20261026,
evidence/pv-runjoin28-20261027/). Option (A) therefore reads: the honest-user domain is spends whose
preparation succeeds, which today requires positive change for both transfers and withdrawals; users
cannot spend a note's entire value in one transaction through the shipped client. The lead's
recommendation is unchanged.


Recount 7 scope update (D332–D345, D353). The honest source handoff covers every
input carrying semantic Admission, a successful full compiler return equal to
its cached compiled payload with both Result layers, Checked, and canonical
frontier words. For every such input its native public and initial semantic
trace equal those of the same canonical target with D18 transport. This is the
source handoff for privacy of users whose prover inputs are produced by the
compiler and satisfy those guards. The adversary, observer, simulator, bound
and bad event retain their original scope. PV_RunJoin_HonestIdentification26
proves these fields, and HonestConsumer26 applies the unchanged consumers;
HonestFixtures26 provides transfer and withdrawal non-vacuity. The raw cached
family still has identification_unsatisfiable; no universal raw-family claim
is substituted. This is information about the discharge route, not an owner
approval of a changed endpoint.

The canonical honest pipeline decodes the snapshot through its codec before
calling the wrapper (D342). The raw withdrawal wrapper can return success on
noncanonical active frontier words, and those payloads fail HonestInput; the
snapshot codec rejects them. Positive change alone is therefore not a sufficient
honesty or preparation-domain characterisation. CanonicalHonest31.transfer/withdrawal now derives the honesty guards from every
successful canonical preparation, and Coverage31.transfer_iff/withdrawal_iff
characterizes that codec-first source route. The source conclusion retains its
canonical codec, pool/deployment and readiness meaning; it is not the missing
native world/ROMView decoder identification. Runjoin33 repaired the stale-cache
endpoint, lane and snapshot audit obstruction. Runjoin34–46 adds body,
serialization and actual-caller-domain proofs, while the full published-proof
Result, native helper effects/decoders and RustRealRefinement composition remain
unfinished at the pins. V244/op227 is still a named undischarged dependency.
The owner domain choice remains open despite this proof progress. Evidence:
LOG D367/D376/D401/D404/D411/D413, the pinned runjoin reports and recount8
CORRECTIONS8.md. These choices unblock a precise successful-user domain and
concrete caller/runtime binding toward V038/V045, not privacy for arbitrary
cached compiler inputs.

The D348 log/error observer coverage decision is open for the verifier and
the deployed client. The question is how every deployed on-chain log and error
byte, and client formatting, diagnostics, panic/error and backtrace channel,
including occurrence on rejection paths, is represented in the endpoint's
observation. View/ROMView, abstract Aux and observer_program provide no selected
total deployed encoding/association. Forwarding the model Boolean decision does
not supply it. D159 includes these observables. This is a coverage gap in the
current statement, not a new trust item or a theorem already proved inside it.

The options are a total representation in the existing observation carrier
with a proved deployed association, or an explicitly approved model extension
with the affected simulation and theorem transport. Omitting published logs,
error text or witness-dependent occurrence would change the adopted observer
and is not approved. The chosen route must include the public execution context
and every observable abort/rejection event, alongside bytes and side channels.

The lead's D348 recommendation is to prove verifier log/error text determined
by public transaction bytes and explicit public context, without allocator
addresses, timing or uninitialized bytes in the text. D414 adds the direction
to trace each formatting entry to its actual caller and guard and classify it
as panic-only or honest-path. There is no recorded lead or owner selection of
a client diagnostic representation, and no recorded claim that these client
channels are all public. The recommendation unblocks a complete observer
specification and the subsequent native determinism or simulation proofs;
approval alone would not establish either property.

D414 identifies core::fmt vtable, vtable_drop_shim, write_str, write_char and
write_fmt glue in the op227 cone. Panic-message construction on bounds/unwrap
failure is a proposed explanation, not a proved exclusion from honest runs.
The candidate's rdeac report and diagnostic-provenance.json identify reachable
deployed-client anyhow::ensure formatting, strerror and UTF-8-lossy error
strings, and backtrace symbolization through build-id, debuglink/debugaltlink,
split-DWARF and addr2line. Known public pieces include the literal69 basename,
public name/join shapes and /proc paths, template capacity shape, and build-id
size arithmetic. Their invocation guards are not thereby public. Comparison
failure/operand lengths, error and invalid-UTF8 guards, selected captured PC,
module/frame/unit/path, cache-miss selection and metadata provenance remain
unclassified. The23 recorded contexts and conservative executable-address
indirect cover are not an exhaustive source reachability certificate.

No admitted same-public witness pair exhibiting different diagnostic events or
text was established. No proof establishes witness independence of occurrence
or content either. Honest-run reachability and witness dependence remain open.
The passing adapter/axioms targets61197/61198 do not close the gap; final endpoint
replay61199 failed and its corrected source is uncompiled. V178/V181 remain
suspended. Public-size allocation failure is already under retained runtime/
allocator primitive adequacy under rdea-1, with explicit failure/post-world
branches; it does not prove public invocation or allocator outcome independence
given earlier private state. V268–V270 do not cover this entire diagnostic cone.

Evidence: LOG D159/D348/D399/D410/D414, recount7/D348.md, candidate
`evidence/pv-rdeac-20261028/REPORT.md` and `diagnostic-provenance.json`, pinned
b3p6 `resume7/RESIDUALS.md`, and recount8/CORRECTIONS8.md. The privacy lead and
owner resolve the representation/contract choice; deployed verifier/client
association remains proof work. The capped T is unchanged.

K-1 and K-2 are evidence corrections, not owner trust-list choices. Exact KMX
patches and matched failing controls are required for copy-dependent Kani
credit; function-pointer forms stay quarantined. Historical three-row KMX
re-credit in D365 does not override deployed-source suspensions. Recount8
accepts22 of23 claimed restoration packets and rejects V213: its only binding
compile41466 is void under ruling(t), and final import audits did not recompile
it. V178/V181 and the remaining native-instance rows stay suspended. These
results preserve their model/source theorems and do not remove endpoint
premises. The compiler, runtime, E1/E2, real RunJoin and L1/L2/L3 boundaries remain.

## Decision: prover timing evidence on a continuously throttled build host (LOG D359, 2026-10-28)

**Question.** The adoption timing gate (median under 15 s and candidate/shipped ratio at most 1.10,
per fixture) was pre-registered to be judged only on unthrottled, interference-free pairs. In a
clean quiet window on the merged candidate 82566acdfb, all 10 paired runs were valid (no foreign
scope in 50 inventories) and all 10 were thermally throttled: transfer median 13.89 s vs 13.92 s
shipped (ratio 0.998), withdrawal 13.90 s vs 13.85 s (ratio 1.004). The host has throttled about a
third of its uptime and on every pair in this window. Evidence: codex/pv-gate6-20261028,
evidence/pv-gate6-20261028/README.md and comparison.json (per-pair thermal counters).

**Options.** (A) Accept paired, alternating, throttled runs as the timing evidence: the measured throttled medians are under15 s and the paired ratios are near1. Treating these data as sufficient would amend the evidence acceptance rule; the samples do not prove a universal unthrottled upper bound or eliminate frequency/order effects from the ratio. (B) Restore the
host's cooling (or use another x86_64 host with the same toolchain) and repeat the window until ten
unthrottled pairs exist. (C) Keep the gate undecided.

**Lead recommendation.** (A) for the ratio and the 15 s bound, recorded as "measured under
throttling, paired", with (B) as a later confirmation if the host's cooling is fixed. The lead does
not change the pre-registered criterion itself; this is the owner's call.

**Unblocks.** The prover candidate's adoption gates (stage A already passes: three ELF pins, pinned
client, fixtures, 1,000/1,000 differential).

**Coverage update (LOG D367): the zero-change domain option (A) has source-level coverage.** On the
canonical preparation route (snapshot codec, then the frozen outer wrapper, then the inner compiler),
the universal V152-V154 honest-family theorem covers exactly the admitted pairs that route prepares;
every successful preparation yields an honest input with no remaining admission hypothesis, and
positive change is necessary for both transfers and withdrawals
(PV_RunJoin_CanonicalHonest31.transfer/withdrawal; PV_RunJoin_CanonicalCoverage31.transfer_iff/
withdrawal_iff; codex/pv-runjoin-20261026, evidence/pv-runjoin31-20261028/OWNER-COVERAGE.md). Under
the zero-change domain option (A), the proposed privacy claim's honest-user domain is therefore exactly "spends the shipped client
prepares", with zero-change spends of either kind outside it. The decision itself is still the
owner's.

## Resolved domain finding (LOG D371/D375): direct library noncanonical limbs

The raw recipient-key limb P versus0 finding is retained for direct library
callers. The shipped JSON planner trace excludes that pair as described below;
this is no longer a pending owner choice. The actual native caller/domain and
observer coupling still belong to the open RunJoin proof.

**Resolved (LOG D375, 2026-10-28): the noncanonical-limb finding is outside the shipped client's honest route.** The trace (codex/pv-l2c-20261028, evidence/pv-l2c-20261028/resume-d371/REPORT.md) found no unchecked path by which a noncanonical limb reaches the compiler through the shipped JSON request planner; decoder and generator bounds and canonical compiler columns are proved, and guard N3 composes on that canonical domain. No owner decision is needed for privacy. Residual, for information: the Rust library API accepts raw noncanonical limbs from direct callers that bypass the client's decoders, which makes such a spend fail (availability only).

## Pending decision (LOG D381, 2026-10-28): extraction compiler cohort versus the shipped compiler

The extraction toolchain (Charon/Aeneas) and the native fixtures behind most candidate closures ran on
Rust 1.98 nightly (nightly-2026-06-01); the shipped client is built with the owner-pinned rustc
1.94.1. A body audit (codex/pv-fscan-20261028, evidence/pv-fscan-20261028/SCAN.md) suspended 41 of 66
candidate closures because reached bodies differ between the two configurations. Where the Rust source
is identical and only compiler lowering differs (class A, being classified now), the native link
holds if both compilers preserve source semantics. **Question:** may class-A rows be credited under
the existing compiler-preservation obligation (row V370), with the compiler cohort recorded as a named
boundary, or must every native link be re-established on the 1.94.1 toolchain itself (which the
extraction tool may not support)? Rows whose std or dependency SOURCE differs (classes B and C) are
being re-checked against the deployed sources regardless. The lead's recommendation will follow the
classification.

**Update (LOG D386): the compiler-cohort question now concerns one row.** Classification of the 41
suspensions found only V242 differing by compiler lowering alone (same Rust source). The other
resolved differences are real source differences in the standard library (23 rows) or a dependency
(2 rows, zeroize 1.9.0), which are being re-verified against the shipped sources and do not need an
owner decision. The fifth amendment labels tool-semantic transport as reclassification and leaves this separate Stream B compiler-cohort choice pending (D396). Recount8 keeps V242 OPEN in owner bucket(c). The question for V242 stands as written above; the lead recommends crediting
lowering-only rows under the compiler-preservation obligation (row V370) with the compiler cohort
recorded as a named boundary, because the alternative (re-establishing every native link on the
1.94.1 toolchain itself) is not supported by the pinned extraction tools.

### Pointer (D416, 2026-10-28): deployed devnet verifier is the historical program

Stream A found that the devnet R1 verifier is immutable and runs the historical fb2fc048, not the proved release (devnet 63ad3e9c, default f8c0ec72), and has put the redeployment question to the owner. No credited privacy result depends on devnet runs. The privacy target is stated for the deployed system, though, so it cannot be claimed until the deployed verifier equals the pinned release ELF. Stream B has no separate decision to ask for here; this pointer only records that the privacy claim depends on the soundness lead's question.


## Release checklist and nonvacuity update, recount8

The release checklist requires the shipped prover to match its proved source,
E1/E2 and real RunJoin, the proof-account client route, L1/L2/L3 evidence, final
adoption/timing gates, a coherent dependency-closure replay and accepted axioms,
and **deployed verifier equals the pinned release ELF**. D416 records the
immutable historical devnet verifier fb2fc048 and matching Pool121f3e29; the
release verifier pins are devnet63ad3e9c and defaultf8c0ec72. This is a deployment
obligation and a pointer to Stream A's owner question, not a new privacy premise
or a decision authorizing redeployment here. No credited privacy row was derived
from historical devnet transaction behavior.

D415 corrects D406–D408: JHx_Joint.source establishes historical-forest
satisfiability only. Its phase/observer carriers differ from the headline;
identity components alone are not a compiled retargeted joint witness. V045,
V046 and V047 retain their existing status. The merged pv-2tnv partial result
constructs a byte-derived transfer13 public statement, canonical matching
witness, append/payment/lane associations in the headline carrier. Native
handles/decoders and exact joint-wrapper association are still missing.
FixturePdaRuntime remains deferred and no AGG16 consumer was staged. The owner
need not approve a mathematical bridge that has not yet been proved.

The full-withdrawal/zero-change domain, paired throttled timing, V242 compiler
cohort, complete log/error observer, release features/CT decoding, N7 custody,
SHA-NI route, DOITM implementation and client scope choices remain open. Client
toolchain selection, D188 narrowing, failure-signal optionB and the capped T
remain approved. O_EXCL atomicity, durable nonce-store fsync/directory persistence
and process-state observation remain named proof/adequacy findings, with no new
trust field silently adopted. Target not yet established.

## Decision requested (D474, 2026-10-29): how to close the client's local diagnostic channel (D348, client half)

**Question.** The D159 observer includes the deployed client's local outputs: stdout JSON, stderr errors, written files, panic and allocation-failure messages, backtraces and crash reports. Eleven proof rounds (pv-diag to pv-diag11) have reduced this channel to fifteen named links (D471). Under the owner's option B (D215), operating-system outcomes are a public signal, and that law is proved (PV_DIAG7.DIAG_optionB_public_signal). Modelled panics are excluded on honest runs wherever a complete-Result theorem exists (D468). The remaining cost is concentrated in one place: binding the Rust standard library's I/O, formatting and cleanup layer (File and OpenOptions, buffered and locked stdout and stderr, thread-local capture, descriptor drop and unwind, backtrace symbolisation) under own-1, so that each channel's actual bytes can be identified. No round so far has discharged a deployed link of that layer. No witness-dependent diagnostic has been found either.

**Options.**
- (A) Keep the code as it is and complete the standard-library I/O association. This is sound and needs no owner change, but it will take many more proof rounds. It is the current default and continues meanwhile.
- (B) Narrow the observer so that the client's local outputs are visible only to the user. NOT recommended: it weakens the observer, conflicts with D159 (side channels are in scope), and would have to be reported as a narrowed result.
- (C) Change the deployed client so that its diagnostics cannot depend on the witness by construction. That means fixed error codes or literal messages with no formatted secret-derived operands, no backtrace capture, a fixed panic hook with panic = abort, and an unchanged stdout JSON whose fields are already public (attempt count via V394, mask_audit fixed by success guards). The privacy argument for this channel then becomes a short universal statement over the client source plus option B. Cost: a shipped-code change under crates/ or the client, which requires the three ELFs rebuilt and an owner-approved repin; client-side only, with no verifier-byte change expected.

**Recommendation: (C)**, because it closes the channel by construction rather than by proving properties of large standard-library cones. If (C) is adopted, the lead will issue a minimal, reviewed client patch with an ELF pin check and a re-run of the timing gate (prover performance budget +10%). Until a decision, (A) continues. **Unblocks:** the three DIAG_* inputs of pv-rj4idb's observation decoder, and with them most of the client half of D348.
