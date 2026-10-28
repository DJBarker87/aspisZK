# Privacy owner decision packet — 2026-10-27 (B)

Target not yet established. Evidence is frozen by the
[recount 7 pins](../evidence/privacy-recount-20261026/recount7/pins.json).
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

The following decisions/actions remain open.

1. **Release recipe and constant-time private-input decoding.** The question is
   whether to adopt ct-host-prover on, insecure-spend-fixture off, a locked build
   with the approved client toolchain, and fixed-width constant-time decoding
   for private input, as recommended in D272/D276. Options are that recorded
   recipe and decoding route, or another explicit recipe/decoder with renewed
   evidence. The historical recipe retains N1; inspected audit B removes N1,
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
   for V231–V238. V233's split law does not resolve this choice. Evidence:
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
limitation goes to the owner as a product question, independent of privacy. The privacy route's
remaining step (successful preparation implies the honesty guards) is needed under either option and
proceeds meanwhile.

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
honesty or preparation-domain characterisation. The exact successful canonical
preparation implies HonestInput theorem is still open at the pinned runjoin32
snapshot, after lane-root progress. Input, append, recipient and sentinel
obligations remain. Neither the domain choice nor the client-scope choice
converts that missing implication into trust. The lead's option A recommendation
from D338/D342 stands; no later owner adoption is recorded in the audited LOG.
Evidence: pinned runjoin evidence/pv-runjoin26-20261027/REPORT.md,
evidence/pv-runjoin28-20261027/GUARDS.md and FINDING.md,
evidence/pv-runjoin31-20261028/LANE-STATEMENT-AUDIT.md and
recovery/RESUME32.md. This clarifies what the domain and client choices unblock:
a precise successful-user coverage statement and a concrete caller/runtime
binding toward V038/V045, rather than a new proof on arbitrary cached inputs.

The D348 observer coverage decision is open. The question is how the deployed
verifier's on-chain log and formatted error bytes on every reached path are
represented in the endpoint observation. The audited endpoint exposes an abstract
View/ROMView and observer_program; no selected total encoding/association ties
all those bytes, including rejection-path bytes, to that observation. Abstract
Aux capacity and forwarding a Boolean decision do not establish this association.
This is a coverage gap against D159, not an extra trust item or a privacy proof
inside the current statement. The options are to specify a total representation
in the existing observation carrier and prove its deployed association, or to
approve an explicit model extension with the affected theorem and simulation
transport work. Omitting published logs would change the adopted observer and
is not an approved option. D348 records the lead's expected route: prove logs
and error text deterministic from public transaction bytes, without allocator
addresses, timing or uninitialised bytes in the text; it records no selected
representation or owner approval. The chosen route must account explicitly for
any public execution context used by the program. This unblocks a complete
observer specification and the subsequent verifier log/error determinism proof.
Evidence: LOG D159/D348 and recount7/D348.md, with immutable endpoint,
FsStatement, ZkStatement, RomObserverBin and RunJoin source witnesses in the
recount 7 manifest. Owner: privacy lead and owner for the contract; deployed
verifier/client association remains a P obligation after that choice.

K-1 is an evidence correction, not an owner trust-list choice. The historical
copy-dependent Kani links of V178, V179, V182, V195 and V233 remain suspended.
Their independent replacements have class structural (K-1 substitute), with the
same statements and residuals. Exact KMX-patched positive gates and failing
matched negative controls are required before Kani re-credit; the pinned kstub
progress does not yet supply all five. V184 stands on its structural proof.
The capped RunJoin T remains exactly its three approved fields.

## Decision: prover timing evidence on a continuously throttled build host (LOG D359, 2026-10-28)

**Question.** The adoption timing gate (median under 15 s and candidate/shipped ratio at most 1.10,
per fixture) was pre-registered to be judged only on unthrottled, interference-free pairs. In a
clean quiet window on the merged candidate 82566acdfb, all 10 paired runs were valid (no foreign
scope in 50 inventories) and all 10 were thermally throttled: transfer median 13.89 s vs 13.92 s
shipped (ratio 0.998), withdrawal 13.90 s vs 13.85 s (ratio 1.004). The host has throttled about a
third of its uptime and on every pair in this window. Evidence: codex/pv-gate6-20261028,
evidence/pv-gate6-20261028/README.md and comparison.json (per-pair thermal counters).

**Options.** (A) Accept paired, alternating, throttled runs as the timing evidence: throttling only
lowers the clock, so a throttled median is an upper bound on the unthrottled time (13.9 s is under
15 s), and pairing under the same throttling makes the ratio a fair comparison. (B) Restore the
host's cooling (or use another x86_64 host with the same toolchain) and repeat the window until ten
unthrottled pairs exist. (C) Keep the gate undecided.

**Lead recommendation.** (A) for the ratio and the 15 s bound, recorded as "measured under
throttling, paired", with (B) as a later confirmation if the host's cooling is fixed. The lead does
not change the pre-registered criterion itself; this is the owner's call.

**Unblocks.** The prover candidate's adoption gates (stage A already passes: three ELF pins, pinned
client, fixtures, 1,000/1,000 differential).

**Update (LOG D367, 2026-10-28): the coverage under option (A) is now proved exactly.** On the
canonical preparation route (snapshot codec, then the frozen outer wrapper, then the inner compiler),
the universal V152-V154 honest-family theorem covers exactly the admitted pairs that route prepares;
every successful preparation yields an honest input with no remaining admission hypothesis, and
positive change is necessary for both transfers and withdrawals
(PV_RunJoin_CanonicalHonest31.transfer/withdrawal; PV_RunJoin_CanonicalCoverage31.transfer_iff/
withdrawal_iff; codex/pv-runjoin-20261026, evidence/pv-runjoin31-20261028/OWNER-COVERAGE.md). Under
option (A) the privacy claim's honest-user domain is therefore exactly "spends the shipped client
prepares", with zero-change spends of either kind outside it. The decision itself is still the
owner's.

## Pending (LOG D371, 2026-10-28): noncanonical witness limbs accepted by the compiler, then rejected by the prover

A recipient owner-key limb written as raw P (the same field element as 0) is accepted by the frozen
forest compiler and later makes the shipped prover fail with Err(Semantic); the canonically written
twin succeeds (codex/pv-l2c-20261028, evidence/pv-l2c-20261028/resume-d369/D370-FINDING.md). A job is
tracing whether the shipped client's input decoders can ever pass such a limb through. If they always
canonicalise or reject, this is outside the honest route and no decision is needed. If not, the
options will be (A) reject or canonicalise noncanonical limbs at decode, which changes frozen client
code and its gates, or (B) restrict the privacy claim's honest domain to canonical inputs. The lead's
recommendation will follow the trace.

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
owner decision. The question for V242 stands as written above; the lead recommends crediting
lowering-only rows under the compiler-preservation obligation (row V370) with the compiler cohort
recorded as a named boundary, because the alternative (re-establishing every native link on the
1.94.1 toolchain itself) is not supported by the pinned extraction tools.

### Pointer (D416, 2026-10-28): deployed devnet verifier is the historical program

Stream A found that the devnet R1 verifier is immutable and runs the historical fb2fc048, not the proved release (devnet 63ad3e9c, default f8c0ec72), and has put the redeployment question to the owner. No credited privacy result depends on devnet runs. The privacy target is stated for the deployed system, though, so it cannot be claimed until the deployed verifier equals the pinned release ELF. Stream B has no separate decision to ask for here; this pointer only records that the privacy claim depends on the soundness lead's question.
