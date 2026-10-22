# S4 indexed powers to S9 N=4 array proof

This packet contains a focused proof that reuses the indexed early-return
`weights::powers<N>` model for the adopted S4 Rust body at `N = 4`, then maps
each returned element into the exact `S9Wide` carrier used by the S9 helper.
The result theorem is
`AspisR1S4IndexedPowersToS9ArrayV1.early_powers4_to_s9_total_exact` in
`sources/S4IndexedPowersToS9ArrayV1.lean`.

The theorem takes a canonical `PowerWide` base. It obtains the `N = 4`
indexed array result and, for every `j : Fin 4`, proves the mapped element is
canonical and decodes to `decode x ^ j.val`. It uses the retained generic
`AspisR1LoopPowers.early_powers_total_exact` proof and the existing
`powerToS9Helper` carrier/canonicality/decode lemmas. It does not assume an
independent output array or per-index law.

The exact adopted Rust binding is checked by `check-source-binding.py`. The
checker requires the merged adoption commit to be an ancestor of the observed
HEAD, verifies the current `weights.rs` bytes against that committed source,
checks the SHA-256 and Git blob, compares the complete `weights::powers`
function body byte-for-byte with the retained S1 candidate's
`candidate_transform.after`, and runs the retained S1 source/model checker.
The check passed with observed HEAD
`9598a0a49d79b1c1323d74ad02e002dd46ef1dbc` and adoption commit
`29cbab431742f7e899870595167efa193a379f0a`. The source file SHA-256 is
`28b558ffa9f5b004188c7f50b1597fe681186f54fb4d52a3bd125df4f2481137`, its
Git blob is `91e3aa767f0330065ac99d93bee2585cf5f8b5f8`, and the exact powers
body SHA-256 is
`79c059dd574e3b0dac53ca40f02072d473466dc58ab231f23636f94285b12a22`.

The proof compile used Lean 4.32.0 with the exact 447-entry full profile
preserved in `receipts/full-LEAN_PATH.txt` (SHA-256
`af764851143725becbb3e22730774fbb5d343a97eb1163cb16e2c66978d7fb12`). Its
first-resolved direct owners and hashes are in
`receipts/profile-manifest.json`. The central compile exited 0 in 19.856 s,
with 3,207,978,816 bytes peak aggregate RSS, 0 swap, and named axioms
`[propext, Classical.choice, Quot.sound]`. The exact command, raw Lean log,
time log, preflight and receipt are retained under `receipts/`. The produced
object SHA-256 is recorded as metadata in `receipts/receipt.json`; the object
itself is intentionally not included.

Attempt 1 failed only on array-index proof bounds and unfolding the
`LoopPowers.decode` carrier definition. Its exact source and Lean error log
are retained under `diagnostics/`; attempt 2 is the accepted compiled source.

This proves the adopted wide-field `weights::powers` operation at N=4. It
does not prove S9 `kpowers`, which still uses `core::array::from_fn`, and it
does not close the separate source-library `from_fn` correspondence or the
complete/frozen S4 caller. The older S1 source checker describes that source
model as a candidate; this packet binds the adopted S4 function body to that
already-extracted model without expanding the model's other claims.
