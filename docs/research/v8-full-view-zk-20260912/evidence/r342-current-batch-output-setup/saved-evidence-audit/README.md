# R340/R342 saved-evidence audit

Read-only consistency audit. No Lean rerun or tracked edit was made.

Both bundle checksum sets, saved source copies, target SHA-256 values, successful logs, resource settings, and full axiom outputs match. R340 compiled at `40a051e060c400dc65d9ada197bdff94d26d8d5b`, an ancestor of current HEAD, with exit 0, 1.06 s, 2,531,348 KiB child RSS and zero swaps. Its four reports show both copied Clone declarations are axiom-free; the two selected output wrappers use only `propext`, `Classical.choice`, and `Quot.sound`. The R292 clone and selected output fragments at lines 183–200, 569–586, and 587–604 match the raw target byte-for-byte; the source SHA is `4d40a5b7…d95aec4`, and no source operation adaptation is recorded.

R342 compiled at `d3d12f9f5540a37f456672f59c07d90d30187da2`, exit 0, 1.66 s, 3,719,400 KiB child RSS, and zero swaps. All nine reports use only foundational axioms. It depends on the exact R340 target SHA recorded in its manifest. Its two model theorem signatures require only nonempty input lengths, canonical reads for indices `1 ≤ j < length`, and prefix reads for indices `< length−1`. The cloned-zero vector, from_elem result, reverse range/endpoints, output length/capacity, and final index-zero safety are derived. No output vector/length, extra capacity, nonzero condition, or successful result is supplied as a premise. The theorem uses pinned Aeneas Std definitions and does not prove independent Rust Std/compiler correspondence, original guards, or whole batch behavior.

Both failed attempts and the original worker draft are preserved. Failed attempt 1: exit 1, 1.56 s, 3,698,736 KiB, zero swaps; attempt 2: exit 1, 1.53 s, 3,704,360 KiB, zero swaps. `sorryAx` appears in rejected outputs only. An initial checker incorrectly required the first theorem’s `hxs/hpx` binder names to appear in the second theorem; the latter correctly uses `hys/hpy`. The initial mismatch is retained in `rejected-audit-initial-hxs-matcher.json`.

Machine-readable result: `audit.json`; reproducible checker: `check.py`.
