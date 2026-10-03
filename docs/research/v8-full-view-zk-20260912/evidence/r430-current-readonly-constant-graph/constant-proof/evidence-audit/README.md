# R430 constant proof attempt-a evidence audit

Read-only audit of `../attempt-a`. No Lean rerun/build and no proof-source edits.

The launch, receipt, staged `source.lean`, and remote before/after source digest all agree: `9bb531624461a6ba3d6605a870f779d5cc603ab670551dd44c3755c718dc7335`. The recorded source revision is `367345a0407f8869375dcd2f30fda36ca6c4dfcb` in both launch and receipt. Six remote output-copy statuses are present and all report exit 0. The raw Lean log has 12 complete `#print axioms` lines, matching the receipt’s 12 reports exactly. Lean is pinned as `Lean (version 4.32.0, x86_64-unknown-linux-gnu, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)` and the remote runner asserts `leanprover/lean4:v4.32.0`.

GNU time and receipt agree: exit 0, wall 0:01.90, max RSS 2541012 KiB, swaps 0. The effective cgroup before/after matches 5 GiB high, 7 GiB max, zero swap, 128 tasks; the saved post-run cgroup peak is 370274304 bytes with zero swap and zero OOM counters.

There is a measurement discrepancy: GNU time reports 2541012 KiB max RSS (2601996288 bytes), while cgroup `memory.peak` reports 370274304 bytes. Both raw values are preserved; the saved evidence does not explain the difference. This audit flags it without replacing either figure.

Detailed source hashes, copy receipts, exact axiom comparison, raw metrics, and pin checks are in `audit.json`. The initial audit’s string-matching false negatives are preserved as `audit-v1-initial-parsing.json`; this report corrects those parsing issues and records the separate RSS/cgroup discrepancy.
