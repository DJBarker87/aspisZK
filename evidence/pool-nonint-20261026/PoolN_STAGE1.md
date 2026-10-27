# Stage 1: first native handler rejection and symbolic size facts

PoolN_KANI001 proves the complete unchanged ASDI handler on valid80-byte
instructions, a192-byte Pool-owned occupied-or-arbitrary primary state slot,
and arbitrary bytes and balance: exact InvalidAccountType, byte and lamport
frame; unexpected CPI is an assertion failure. This is the primary-role class,
not all ASDI roles, arbitrary account lists or complete dispatch closure.
PoolN_KANI004's192-byte ASPX core-plan harness passed, but the paired1768-byte
harness timed out: overall attempt failed, no paired closure credit.

Failures retained: KANI002 Rust borrow-lifetime errors in the added token parser
harness; corrected by dropping the Ref before checking the underlying buffer.
KANI003 complete ASDI1768 and KANI004 ASPX1768 timed out at60s. Neither is
rerun unchanged or with a larger limit. Replacement splits frame observation:
an arbitrary symbolic byte index tests a single arbitrary pre/post byte of the
fully arbitrary buffer instead of duplicating/comparing the whole1768 bytes.
This retains universal byte coverage, without a1768-byte equality formula.

PoolN_Guards different_size/prepared_rejects/page_rejects compile in
PoolN_LEAN002 with only propext, Classical.choice, Quot.sound. They are explicit
guard-level mathematical/source-summary theorems; no whole-handler source
refinement is claimed. LEAN001 failed on use of the reserved field name meta;
its error-elaborated sorryAx output is rejected, not accepted theorem evidence.

Per-attempt exact target/command, source/dependency hashes, revision, exit,
wall, peakRSS, swap and axioms are in receipt.json/time.log/stdout.log.
Caps unchanged; no package or unchanged full replay. At this stage Lean2/100,
Kani4/40 complete (later pending runs are accounted in their receipts).
No assumptions discharged globally, new trust introduced or release row closed.
All shipped source remains unchanged; ELF rebuild trigger has not fired.
