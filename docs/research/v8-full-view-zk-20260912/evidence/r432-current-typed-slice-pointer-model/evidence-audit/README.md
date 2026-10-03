# R432 saved compilation custody audit

Read-only audit of the saved A/B/C attempts. No Lean command was rerun. Run `python3 verify_attempt_c.py` from any directory to recheck attempt C's saved source hash, target/revision receipt, complete axiom output, GNU time metrics, source before/after hash and effective cgroup settings, and copy-status receipts.

Attempt A (`21ecd749...02c4f9`) compiled the 8-lemma predecessor: exit 0, 1.61 s, GNU peak RSS 2,545,852 KiB, swap 0. Its saved 8 axiom lines use only `propext`, `Classical.choice`, and `Quot.sound`.

Attempt B (`7c7b4027...ad0efc`) added the bridge but failed with exit 1 after 1.88 s, GNU peak RSS 2,541,012 KiB, swap 0. The saved diagnostics identify `Aeneas.Result` / `Aeneas.Result.ok` as unknown, and its failed proof output contains `sorryAx`. It is rejected history and is not evidence for the theorem.

Attempt C (`29e8517d...f47717f`) changes the type references to `Aeneas.Std.Result`. The saved run exited 0 in 1.90 s, with GNU peak RSS 2,552,236 KiB and swap 0. Its 12 complete `#print axioms` reports match the receipt line-for-line and contain only `propext`, `Classical.choice`, and `Quot.sound`. The source hash recorded by the runner and by the post-run snapshot matches the exact saved `source.lean`. The captured scope limits are MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, TasksMax 128; before/after cgroup event counters show no OOM. GNU process peak RSS and cgroup `memory.peak` are reported separately and are not required to match.

This is a generic typed pointer-fragment model result. It does not prove the actual Rust slice source, actual pointer/aliasing behavior, iterator source execution, or any broader release boundary. The semantic/release decision remains with the lead.
