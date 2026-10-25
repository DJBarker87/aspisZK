# S1 native Prepared::new with actual gamma powers, 2026-10-25

Target not yet established. This focused result removes the whole `weights::powers`
cut from the earlier native constructor check. It does not close the enclosing SDK
refinement or S1/S6.

## Before and after

Before: native `Prepared::new`, under six normal-return child cuts including
`powers`, checks the transcript call sequence, query and claim errors, scratch
address and all output fields (accepted packet `s1-native-prepared-20261025`, v6).

After: `verifier::proofs::prepared_new_s2_native_powers` executes the exact frozen
`powers::<29>` body inside the same native constructor. The five other cuts remain:
Transcript new/scalar/queries/scalar_k and prepared_claim. A primitive
`WideExact::mul` normal-return cut supplies symbolic canonical results. It checks
exactly 28 ordered multiplication calls, each with the same row-27 gamma and the
previous output, starting from ONE. The resulting 29 entries and the same caller
scratch address reach prepared_claim. Query failure performs no multiplication or
scratch writes; claim failure preserves the completed scratch, and success checks
the complete native Prepared value and transcript state.

All prior S2 view framing restrictions remain: correct frame lengths, folded root
present, native release Verified with arbitrary observed fields/messages, private
canonical WideExact values. This is control correspondence for the chosen domain
and ordinary child returns, including both errors; not arbitrary-input TOTAL
execution and not a native multiplication theorem. The first expected powers
entry is ONE because the source assigns ONE, not an extra restriction on gamma.

## Source and carrier audit

Historical component snapshot is `25866ec331cc7ce27dd9956609c11d32fa8fa58a`, including
the adopted early-return powers overlay. The factored weights module is not the
whole production file; its complete powers function is byte-identical to the
frozen function. source-binding.json records both full frozen-file and factored
file hashes, exact function text/hash, and unchanged native modules from v6.
All selected native constructor/carrier bodies retain their existing freeze pins.

The release Verified has nine fields. round_checks, terminal and masked_terminal
are prover-only cfg fields in the frozen source; their absence in this release
harness is not a missing release carrier field. This audit does not prove the
full SDK/ABI installation.

## Validation and resources

Only the changed target was compiled, then verified, against the warm two-package
Kani workspace. Kani 0.67.0, rustc 1.93.0-nightly (53732d5e0), optimized MIR/codegen
flags, exact tools/import/source/command pins and immutable source snapshots are
recorded in attempts s1-native-prepared-powers-v1/v2. One atomic shared compiler
lock, 4 GiB sampled aggregate RSS guard, 180 seconds; no NUC or SBF build.

Compilation: exit 0, 1.133886958 seconds, peak RSS 399474688 bytes, aggregate sample
430718976 bytes, zero swaps. Verification: exit 0, 33.280948500 seconds, peak RSS
1619935232 bytes, aggregate sample 2022195200 bytes, zero swaps; 0/1655 failed,
3/3 covers. Default checks with unwinding assertions, no initialization mode.
`#print axioms`: not applicable, no Lean theorem or new axiom. Existing negative
scratch-address check is reused; no unchanged replay. Source-only packet excludes
GOTO programs and all compiled artifacts.

## Remaining and next connection

The primitive arithmetic and five higher-level normal-return cuts are retained;
concrete hash/oracle behavior, initializedness and allocator effects, the SDK
borrow/extraction/runtime installation, actual enclosing caller theorem and
release artifact joins are not discharged. This native result does not remove
SourceCuts or AeneasExtraction from the conditional SDK theorem. Existing Lean
powers/arithmetic and same-caller trace proofs remain separate until that
transport is established. The lead owns coherent enclosing SDK import/re-pin;
S2 remains transferred. No frozen source changed and no candidate adoption or
new source decision is requested by this result. S1/S6 remain open.

## Later-build pin correction

These receipts retain historical component25866 pins. The current release
ledger identifies later build source4bb3b3f51e; see
[S126-FREEZE-RECONCILIATION-20261025.md](S126-FREEZE-RECONCILIATION-20261025.md)
for exact unchanged selected items and changed lower/core/adapter contexts.
No whole-release/source transport is inferred from these historical checks.
