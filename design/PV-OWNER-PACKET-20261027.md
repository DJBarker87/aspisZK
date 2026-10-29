# Privacy owner decision packet — 2026-10-27 (B)

Target not yet established. Evidence is frozen by the
[recount 9 pins](../evidence/privacy-recount-20261026/recount9/pins.json).
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

The open items at recount9 are the client diagnostic design (D474), the
headline observation interface (D478), the successful-user/zero-change domain,
paired throttled timing, V242 compiler cohort, release features and constant-time
decoding, N7 custody, SHA-NI, DOITM implementation and client scope. No adoption
of D474 or D478 is recorded at the pins. D474 recommends fixed diagnostics,
no backtrace capture and a fixed aborting panic hook, with reviewed client
change, ELF checks, repin and timing re-run. D478 recommends an event-retaining
headline and joint simulator composition. The decision texts below are unchanged.

The present headline remains conditional on RustRealRefinement and sees only
the returned Result. It does not establish joint privacy for D159's ordered
outputs, failure/divergence prefixes and timing. The prove_wall_seconds source
witness and conditional clock theorem show why Result-fibre recovery cannot
supply that observation on a good completed path. No paired native non-bad
execution was certified and no witness-dependent timing leak is claimed.
Experimental EVHD is separate and unadopted. Its later progress is outside the
recorded snapshot.

The diagnostic line is paused after diag12 pending D474; no deployed DIAG link
was discharged. V239 is parked after ownp, with SourceDense proved and four
deployed links open. Rjdec/rj4idb are parked with conditional decoder/factorization
results. L1 counts and the publication theorem have compiled skeletons with
open native/joint links; op227 and L2E remain in progress at their pinned heads.
These decompositions organize proof work and do not close the endpoint.

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
endpoint, lane and snapshot audit obstruction. Runjoin34–54 adds body, serialization, weight-constructor, opening and publication
composition results. RUNJOIN_PUBLISH_COMPACT is conditional on named links:
R24Sampler is proved; CommonSample, BackendInput, FinishContext, QueryAppend,
NodeAppend and PublishOrder remain open in the recorded runjoin54 result.
Native/toRP composition remains unfinished. V244's reference and installed
callback nonvacuity is now proved at model/original-carrier scope; its complete
native binding, D188 and library coverage remain open. The op227 hypothesis is
not discharged.
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

D474 and D478 now state the representation and implementation choices explicitly.
The lead recommends D474(C) and D478(1). The complete D159 observer remains the
target; neither narrowing nor a client change has been approved at these pins.
Public transaction/context determinism remains a useful verifier-side route.
Client diagnostics have conditional option-B event laws and three typed DIAG
skeletons, with fifteen named links. None of the deployed producer links was
fully discharged through diag12. The reusable syscall, buffering and partial
write laws retain EINTR, errors and pending-delivery prefixes; they are not
complete std I/O, format, capture, cleanup or honest joint-distribution bindings.

The inspected op227 fmt glue is panic-only on the scoped honest source route,
with model complete-Result panic exclusions. This does not exclude every panic
or diagnostic in the deployed client. Error/formatter operands, logger levels,
captured PCs and frames, TLS, unwinding and native writes still need actual
bindings and original-L1 coupling. OptionB makes environmental outcomes public
subject to V400's witness-independence P obligation; it does not make secret
operands, whole prefixes or elapsed time public inputs by declaration.

No admitted same-public witness pair showing different honest diagnostics was
established, and no universal native occurrence/content independence was proved.
V178/V181 remain suspended despite the repaired rdeac focused replay62002.
Allocator failure and post-world remain under rdea-1 with their explicit public
failure-event obligation. D348 has both client and verifier coverage remaining.
Evidence: LOG D425/D432/D456/D458–D479 and recount9/CORRECTIONS9.md.

K-1 and K-2 remain evidence corrections. Exact KMX patches and matched failing
controls govern copy-dependent Kani credit; function-pointer forms remain
quarantined. Recount9 confirms scoped restorations V229/V230 under own-2 triple-prime
with the deployed-configuration harness label, V256/V257 after the exact-path
replay, and V260/V265/V217 under own-1. V213's compliant binding, restoring law
and focused audit restore its scoped source/Result credit; seventeen aggregate
consumers remain unfinished. The36 b3p6 raw-model associations are reclassification
within existing tool trust, not V244 closure. No endpoint premise is removed.
The V2 proof-only source supersession is resolved under h5''; it changes no
statement and does not settle the separate observation-carrier finding.

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


## Release checklist and nonvacuity update, recount9

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
V046 and V047 retain their existing status. The pv-2tnv partial result constructs a byte-derived transfer13 public statement,
canonical matching witness and append/payment/lane associations. Rj4idb proves
the byte-pinned typed caller equality and consumes V047's fibre without that
equality hypothesis. Live native record/handle binding and FixturePdaRuntime
remain; a joint native headline instance is not obtained.
FixturePdaRuntime remains deferred and no AGG16 consumer was staged. The owner
need not approve a mathematical bridge that has not yet been proved.

The pending choices are listed in the refreshed summary above. Client toolchain
selection, D188 narrowing, failure-signal optionB and the three-field T remain
approved. O_EXCL, durable nonce-store persistence, world/ownership and process
state remain proof/adequacy obligations. Source membership, leaf restoration
and skeleton compilation do not establish the deployed privacy target.

## Decision requested (D474, 2026-10-29): how to close the client's local diagnostic channel (D348, client half)

**Question.** The D159 observer includes the deployed client's local outputs: stdout JSON, stderr errors, written files, panic and allocation-failure messages, backtraces and crash reports. Eleven proof rounds (pv-diag to pv-diag11) have reduced this channel to fifteen named links (D471). Under the owner's option B (D215), operating-system outcomes are a public signal, and that law is proved (PV_DIAG7.DIAG_optionB_public_signal). Modelled panics are excluded on honest runs wherever a complete-Result theorem exists (D468). The remaining cost is concentrated in one place: binding the Rust standard library's I/O, formatting and cleanup layer (File and OpenOptions, buffered and locked stdout and stderr, thread-local capture, descriptor drop and unwind, backtrace symbolisation) under own-1, so that each channel's actual bytes can be identified. No round so far has discharged a deployed link of that layer. No witness-dependent diagnostic has been found either.

**Options.**
- (A) Keep the code as it is and complete the standard-library I/O association. This is sound and needs no owner change, but it will take many more proof rounds. It is the current default and continues meanwhile.
- (B) Narrow the observer so that the client's local outputs are visible only to the user. NOT recommended: it weakens the observer, conflicts with D159 (side channels are in scope), and would have to be reported as a narrowed result.
- (C) Change the deployed client so that its diagnostics cannot depend on the witness by construction. That means fixed error codes or literal messages with no formatted secret-derived operands, no backtrace capture, a fixed panic hook with panic = abort, and an unchanged stdout JSON whose fields are already public (attempt count via V394, mask_audit fixed by success guards). The privacy argument for this channel then becomes a short universal statement over the client source plus option B. Cost: a shipped-code change under crates/ or the client, which requires the three ELFs rebuilt and an owner-approved repin; client-side only, with no verifier-byte change expected.

**Recommendation: (C)**, because it closes the channel by construction rather than by proving properties of large standard-library cones. If (C) is adopted, the lead will issue a minimal, reviewed client patch with an ELF pin check and a re-run of the timing gate (prover performance budget +10%). Until a decision, (A) continues. **Unblocks:** the three DIAG_* inputs of pv-rj4idb's observation decoder, and with them most of the client half of D348.

## Decision requested (D478, 2026-10-29): the privacy headline's observer must become event-retaining

**Finding.** The headline R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed reaches the deployed system through one premise, RustRealRefinement. Its observer functions (Runtime.disclosed and Runtime.observerOracle) see only each run's returned Result: the publication step and final state. The deployed observation that D159 requires is richer: published bytes plus side channels, including ordered events, partial output before a failure, and timing. pv-top (D476) found the mismatch. pv-fib proved in Lean that it cannot be closed inside the current interface, even when restricted to honest runs outside every charged bad event. The witness is concrete: tools/r1-cost-probe/src/bin/devnet_spend/plan.rs reads Instant::now() at line 84 and prints started.elapsed() as prove_wall_seconds at line 129, after the proof is computed. Two honest runs that differ only by a pause before that read have the same Result, the same public input, the same coins and the same option-B signal, but different observations. This is NOT a leak: timing is meant to be simulated by the level-1 timing model (D163, D166). It means that the current headline, as stated, is a theorem about a Result-only observer. Removing the printed field would not fix it, because an observer can time the process externally.

**Options.**
- (1) Adopt an EVENT-RETAINING observer interface for the headline. The observer receives the ordered event trace, including failure and divergence prefixes and timing observations. The model-level headline is then re-proved for it: the simulator must also produce the trace, using the D163 coupling, the D166 simulatable timing and the option-B public failure signal. This is a strengthening, giving joint privacy against the D159 observer. Its cost is model-level re-proof at the observation layer. Most component results carry over (pv-rj4idb's lossless decoder, the DIAG and L1 skeletons). An experimental draft (pv-evhd, not adopted, separate modules) is estimating the delta now.
- (2) Keep the Result-only headline, and prove separate side-channel theorems plus a composition theorem. Not recommended: separate marginal results do not establish joint privacy (AGENTS.md), and a composition theorem strong enough to be sound amounts to option (1).
- (3) Report the headline as covering a Result-only observer. Not recommended: it narrows the observer below D159, so it would have to be reported as a weaker, different theorem.

**Recommendation: (1).** It is the only option that gives the privacy target as defined. **Unblocks:** installing the observation decoder (pv-rj4idb), and with it the runjoin step (4), L1 and DIAG compositions, and V045. Until a decision, the component lines continue; none of their work depends on the choice, because all of them already produce trace-level results.

### Addendum to D478 (2026-10-29): cost evidence from the experimental draft pv-evhd

An experimental, NOT ADOPTED draft (branch codex/pv-evhd-20261029, head 438524d32b; separate PV_EVHD_ modules; the real headline, Runtime, simulator, observer and bound untouched) compiles a conditional event-retaining headline in Lean. It reuses simE, core_privacy and privacy_transport unchanged, with standard axioms only, and the SAME bound expression. If the joint trace, timing and public-failure links hold EXACTLY, the old bound is retained verbatim and no extra term is forced. If only approximate simulation is available, the draft states the old bound plus an explicit joint trace term (deltaTrace), and the old 2^-100 conclusion would not then transfer automatically. The remaining obligations are named links: the D163 coupling including native trace acquisition, the ordered-event context with timing slots and failure prefixes, the D166 joint timing law on the same coupling, option-B signal independence, causal-prefix and observer-program consistency, and the nine existing acquisition inputs. The draft estimates 3-8 person-weeks of integration and joint-model work, excluding unfinished native leaves, with substantial uncertainty. It notes that option (2) needs the same joint links, so it saves no cost, and that option (1) removes an installation task that is impossible under the current interface. Full detail: evidence/pv-evhd-20261029/COST.md and REPORT.md on that branch. The recommendation of (1) stands and is strengthened.
