# S2-T stage 1: production library pins

Production Cargo.lock is byte-identical to the retained S10 adopted-ELF rebuild
workspace lock (SHA-256 5782e6a3...). Both SDK crates are 2.3.0; cached crate
archive hashes match lock checksums. production-pins.json pins complete source
files and inclusive source spans. The production adapter imports the
solana-program re-export of solana-account-info.

The SBF source is the installed platform-tools v1.52 core/cell.rs, not the
v7 Kani nightly source. RefCell uses an isize BorrowCounter. Ref and RefMut
contain BorrowRef/BorrowRefMut; structural Drop invokes those counters' Drop.
Ref has no DerefMut. The installed rustc reports commit-hash unknown; version.md
names the Anza source commit, but compiler/source correspondence remains P6.
This limitation must travel with the trust pin.

Target: source pin collection only. No compilation or proof run, hence wall/RSS/
swap/axioms are not applicable. Source revision and inherited build references
are in production-pins.json and ../s10-repin-20261022/build-default-v2/.
No release artifact changed; default 40dc7574..., devnet 12cb0bc2..., Pool
121f3e29... evidence is reused, not rebuilt or re-certified here.

No assumptions discharged. Route B retains the newly authorized SDK trust
boundary and P6/runtime/library-source correspondence. Next: exact universal
fifteen-field interface, concrete consistency model, Kani spec and audit.
Budget used: Lean 0/100, Kani 0/60. No shipped-file changes.

# Stage 2: universal fifteen-field interface

S2TrustedSdkBorrow.lean defines the exact fifteen names over a typed Library
interpretation relation, Valid heap/counter/external-borrow/linear-token ledger,
and Enabled operations. The record supplies primitive observations and operation
simulation, not any adapter conclusion. The ambient carrier is arbitrary and
unchanged by the reference primitives. Only bounded exclusive element writes
change payload contents. Aliased data cells are supported; runtime admission
separately supplies data/lamports separation. No production Library instance or
initial relatedness theorem is claimed.

model_satisfies proves all fifteen fields jointly for the identity interpretation
on mathematical heaps, universally over valid local states. This is consistency,
not SDK certification. Its axioms are [propext, Quot.sound]; model_matches has none.
Lean attempts 001/002 failed on syntax/inference (their sorryAx diagnostics are
error-recovery artifacts, not accepted proofs); corrected source passed 003.
Exact command/source SHA/exit/wall/RSS/swap/axiom lines are in lean-*/receipt.json.
All runs used pinned Lean 4.32.0 via lake env lean, one module per capped scope.
No full manifest replay is appropriate for these independent new modules.
Budget used: Lean 3/100, Kani 0/60. Next: inhabited consistency schedules and Kani.

# Stage 3: inhabited consistency and schedules

S2TrustConsistency.lean proves initial_valid for every signed admitted external
counter (including negative conflicts and MAX), shared schedules with two aliases,
failed exclusive acquisition, one move, reverse drops, exclusive move/write/drop,
shared conflict, saturation and error movement/drop. consistency combines the
fifteen-field model witness with a valid concrete initial state. No SDK relation
is discharged. Axioms: initial_valid/consistency use only propext,
Classical.choice, Quot.sound; three schedule theorems have no axioms.
Attempt 004 had local syntax/lemma-name errors; repaired module passed 005.
No timeout or memory kill. Budget used: Lean 5/100, Kani 0/60.

# Stage 4: executable Kani specification and verified-stub use

kani-spec is a standalone cfg(kani)-only evidence crate, not a shipped crate
change. It implements the same primitive transitions in the bounded projection
CELLS=2, TOKENS=3, WIDTH=2, with arbitrary payload/descriptor/ambient values and
full i64 counters. step's independently stated primitive_relation contract checks
exact Result arms, counter/token identity, the complete primitive footprint and
successor validity. Larger instantiations need their own checks; no production
buffer or implicit-Drop wrapper is certified by this small model.

All fifteen named property harnesses passed as individual jobs with complete
wall/RSS/swap receipts, plus step_contract and verified_stub_schedule: 17 unique
passing checks. The latter uses stub_verified(step) through exclusive acquisition,
a conflicting shared acquisition, move and drop; its cover is reached. Source v2
and final primitive/contract/property declarations are identical. The sole final
source delta adds the missing fresh error-token admission to the consumer harness,
which was checked on the final source. The audit stage retains that exact diff.

Attempt history is retained, not promoted: 001 could not find rustc until PATH
was supplied; 002 hit the std aggregate-comparison memcmp unwind bound, repaired
by explicit bounded field comparisons; 005 required enabling -Z stubbing.
Batch004 stopped at its 600-second cap after thirteen property successes, during
cell_payload; account_data_cell had not started. It was never rerun as a batch.
007/008 isolated the unfinished tail. Because timeout lost trustworthy child RSS,
009--021 individually repeated ONLY the thirteen completed checks to replace
missing resource artifacts (the explicit AGENTS.md missing-artifact exception).
No cap increased; no memory kill occurred. Batch004/measurement-note.json marks
its misleading wrapper-only time RSS unusable. All accepted property results now
have complete independent resource receipts; the failed batch remains history.

Rust compilation used explicit optimized dev profile opt-level=3, confirmed by
Kani's '[optimized]' output. The named expensive step was SAT verification, not
proof generation/elimination. Every compile/proof was scoped at 6G high/8G max,
swap0/tasks64; each new scope had resource admission, with at most four 8G scopes
in the metric pass, below 55G. Maximum accepted Kani peak RSS was 3513488 KiB,
zero swaps. No key/account cleanup or other worktree mutation occurred.

The final consistency module also replaces the two numeral-bound decide proofs
with symbolic omega proofs; focused attempt006 passed with the same standard
axiom set. Budget: Lean 6/100; Kani 21 command invocations, conservatively charged
35/60 including failed invocations, unstarted batch tails and metric replays.
Next: final conclusion-hiding/source/release-pin audit and handoff manifest.

# Stage 5: audit and final handoff

Audit entrypoints (read-only validation; no prover replay):

- `python3 evidence/s2-trust-20261023/audit.py` from the research directory.
- `python3 evidence/s2-trust-20261023/pin_sources.py` refreshes source/hash indexes.
- `python3 evidence/s2-trust-20261023/finalize.py` validates accepted proof receipts.

AUDIT.md inspects all fifteen full statements and their transitive local
definitions. audit.json confirms the exact field inventory, only Std imports,
no forbidden proof devices, every new theorem's axiom print, and the allowed
new-module/evidence-only change set. No field mentions caller success, fixed
caller bytes, outputs, logs, dV_frozen2 or S2CallerFacts. Primitive arbitrary
slice contents and library Result arms are explicitly distinguished from caller
conclusions; they are required local semantics, not a hidden accepted observation.

production-pins.json now additionally pins the actual S10 rustc argv, the SBF
core/std archive checksums/sizes, the installed std::cell re-export at std/lib.rs
line491, separate Ref/RefMut type/deref/drop spans, adapter/workspace manifests,
and all three adopted rebuild commands/artifact comparisons. The SDK lib.rs
snapshots match the checksum-verified crate archives. The adopted lock and
adapter source/manifest match the read-only S10 rebuild workspace. No diagnostic
v7 lock is substituted. The SBF compiler still reports unknown source commit;
version.md's Anza commit/source presence does not prove prebuilt core/compiler
correspondence or prebuilt core feature configuration. Those remain visible P6
limits; the binaries and installed source are separately pinned.

Exact established claims:

- `AspisR1.S2Trust.model_satisfies`: the fifteen-field trust structure is jointly
  satisfiable over every valid related mathematical local state (arbitrary ambient
  carrier), not only a selected successful acquisition.
- `AspisR1.S2Trust.consistency`, initial_valid and the three schedule theorems:
  admission is inhabited and failed borrows, moves, drops and writes are included.
- Kani `step_contract`, fifteen named properties and `verified_stub_schedule`:
  the bounded executable spec satisfies its primitive relation; verified stubs
  support the checked schedule. Every final accepted result has exact command,
  source/dependency/tool pins, exit, wall, RSS, swaps and axiom status. See
  manifest.json and its accepted_lean/accepted_kani receipt lists.

Discharged: joint satisfiability/non-vacuity of the proposed model interface.
Retained: the already approved SDK/std typed interpretation trust, initial
runtime/heap/provenance admission, P6 source/compiler/runtime binding and every
caller/common-execution/Required14/child-effect/history/binary obligation.
No extra trust ruling, new release metric, SDK certification or S2 closure is
claimed. Final Rust consumer-only admission delta is retained in
rust-harness-delta.diff; primitive/contract/property declarations are unchanged,
so no old result is silently attributed to a changed callee.

Validation actually run: focused new Lean modules; axiom prints for all seven
new theorems (including the private helper); 17 unique accepted Kani checks;
source/lock/archive comparisons; field/proof-device/change-scope audits. Reused:
Std compiled cache, the unchanged primitive proof closure after the consumer-only
edit, and the three S10 adopted ELF rebuilds. No full frozen manifest or unrelated
runtime/adversarial suite was repeated. Raw tool logs preserve their whitespace;
format checks on authored source/documentation are separate from raw receipts.

Remaining blocker / next deliverable: instantiate the production typed Library
relation and initial admission, prove unchanged-caller per-call/implicit-cleanup
simulation and the E-indexed common execution certificate. Larger Rust projection
capacities require fresh checks before use. Then fill Required14 and compose the
actual child/effect/runtime/source/binary joins. S2 remains OPEN; target not yet
established. No shipped file changed, so release ELFs were not rebuilt again;
default40dc7574..., devnet12cb0bc2..., Pool121f3e29... pins remain unchanged.
All this worker's host jobs are terminal. No push, merge, other-worktree mutation,
or key cleanup occurred. Final budget: Lean6/100; Kani21 invocations, charged35/60.
