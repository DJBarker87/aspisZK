# Privacy owner decision packet — 2026-10-27 (B)

Target not yet established. These seven decisions/actions remain distinct from
proof work. D248 already adopted the capped three-field RunJoin trust list and
option B; neither adoption proves a native instance. Evidence below is read at
[recount-5 pins](../evidence/privacy-recount-20261026/recount5/pins.json); branch-only
files are identified by branch and path. No choice in this packet is adopted.

1. **Client toolchain.** The question is which exact native client build to pin.
   Options are the recorded rustc/cargo 1.94.1 commits, x86_64-unknown-linux-gnu
   and recorded RUSTFLAGS, or a different explicit toolchain with renewed evidence.
   D270 recommends the recorded toolchain, with no target-cpu change, recorded in
   a client rust-toolchain file and release ledger and re-confirmed at adoption.
   This unblocks an identifiable release client binary and its L3/timing evidence.
   Evidence: LOG D269–D270; `design/RELEASE-LEDGER-20261025.md`, native-client subsection.

2. **Release client recipe.** The question is whether to adopt the recommended
   candidate build: ct-host-prover on, insecure-spend-fixture off, locked build
   and pinned toolchain. Options are that recipe or another explicit recipe
   requiring its own audit; the historical recipe retains N1. D272/D276 recommend
   the CT recipe; audit B removes N1, while N2–N6 remain L2 proof obligations.
   This unblocks the final binary audit and preregistered V374 timing experiment
   after integrated route binding. Evidence: LOG D272/D276/D278;
   `codex/pv-l3-20261026:evidence/pv-l3-20261027/dual/AUDIT.md` and
   `design/RELEASE-LEDGER-20261025.md`. Disabling the fixture feature does not
   remove the tool's internally constructed note fixtures.

3. **N7 signing-key custody repair.** The question is whether to adopt the
   prepared raw 64-byte keypair pipe and fixed-copy Rust decoder, or retain
   decimal parsing while preparing another measured repair. D272 recommends
   fixed-width private-input decoding; D283/D284 prepare that remedy for review.
   D284 corrects N7 to signing-seed custody, not witness privacy. Adoption
   unblocks client/signing-boundary integration and the remaining custody audit;
   Python parsing/storage, OS I/O, validation and signing still need treatment.
   Evidence: LOG D283/D284;
   `codex/pv-n7-20261027:design/PV-N7-20261027.md` and
   `evidence/pv-n7-20261027/patches/0001-private-key-raw-fd.patch` on that branch.

4. **SHA-NI semantics and timing.** The question is whether instruction semantics
   may become a trust item or must be proved under the capped T, versus selecting
   a soft backend with its timing cost and adoption gates. D273 records the
   worker's recommendation to retain SHA-NI and prove refinement, and flags the
   semantics trust question for the owner; it supplies no separate explicit lead
   selection. The dispatcher packet says assumed intrinsic correctness is not
   allowed by current capped T. Its +5.93 s / 19.6–19.9 s soft estimate exceeds
   the gates; this is a projection, not a measured whole-prover gate failure.
   A decision unblocks the dispatcher/instruction refinement route for V231–V238.
   Evidence: LOG D263/D273; `codex/pv-cblib-20261027:design/PV-SHA-DISPATCH-20261027.md`.

5. **DOITM implementation.** The question is how to carry out the already adopted
   DOITM-only acceptance of V371. Options are a firmware/kernel/Secure Boot
   configuration permitting enablement and verification, or retaining V371 as
   unresolved while DOITM is off. D248 recommends and records owner acceptance
   only in DOITM mode; raw MSR writes are blocked by Secure Boot lockdown.
   This unblocks the physical instruction-timing transfer, not the L2 laws.
   Evidence: LOG D248; `design/PRIVACY-LEDGER-20261026.md`, Owner decisions section;
   `codex/pv-l2b-20261027:evidence/pv-l2b-20261027/V371.md`.

6. **Extraction past Drop.** The question is whether to authorize larger
   Drop-free prover-local rewrites or a newer extraction toolchain with destructor
   support. D280 requests representative Drop-free measurements before asking
   the owner; no final preference is recorded, and a translator re-pin is not
   approved. The pinned route2 resume has interim probes, not a completed generic
   equivalence or integration result. This unblocks the remaining heap-owning
   callback source laws and caller copies. Evidence: LOG D280;
   `codex/pv-route2-20261027:design/PV-ROUTE2-20261027.md`, Drop-free resume.

7. **Client scope.** The question is whether the release scope is the pinned
   devnet fixture harness or a user wallet taking witnesses from user notes.
   D284 records the question without recommending either scope. The current
   client constructs fixture witnesses; source pins do not establish a user
   wallet. A decision unblocks the concrete client/witness interface and its
   required execution, custody and privacy binding work. Evidence: LOG D284;
   `codex/pv-n7-20261027:evidence/pv-n7-20261027/INVENTORY.md` and
   `design/PV-N7-20261027.md` on that branch. The privacy target remains unchanged.
