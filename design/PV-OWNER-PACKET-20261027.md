# Privacy owner decision packet — 2026-10-27 (B)

Target not yet established. Evidence is frozen by the
[recount 6 pins](../evidence/privacy-recount-20261026/recount6/pins.json).
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
   results supply non-vacuity instances, not the universal V152–V154 source
   identification or V038 common-sample law. Choosing scope unblocks a concrete
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
