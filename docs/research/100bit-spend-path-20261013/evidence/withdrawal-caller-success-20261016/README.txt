Actual ASWP encoder first-bind proof, Lean 4.32

Source: lean/ExtractedWithdrawalCallerSuccess.lean, exact generated mirrors from
173c8fe96 (extraction evidence remains withdrawal-caller-extraction-20261016).
The actual encode_pool_v1_withdrawal_public_v1 p success implies the actual
validate_pool_v1_withdrawal_public_v1 p success for the identical nine-field p.
The exact validator error is also propagated. This removes an assumed helper
success at this encoder boundary. It does not prove verifier/ASF8 reachability,
ASWP encoder totality/byte format, or Rust-to-Lean extraction correctness.

Generated Types/Funs passed in 1.611/1.814 seconds. The final proof passed in
1.611 seconds, peak process RSS 2,636,840 KiB, sampled cgroup 616,116,224 bytes,
process/cgroup swap zero. All four requested audits use only propext,
Classical.choice, Quot.sound. Each job used 6 GiB high/8 GiB max/swap zero.

caller-a failed only in the optional exact-error theorem because the simp
argument named FromSame rather than FromSame.from; this failed source/log/audit
is preserved. caller-b checked the corrected file and reused generated2.
The archive contains exact source snapshots, runner/runtime/import pins, both
attempts, final receipts and proof object. No unchanged predecessor replay.
archive-members.json hashes every one of its 43 regular members.
