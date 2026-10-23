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
