# D432 resume9 — partial structural binding; V244 remains open

Same worktree `/Users/dominic/ZK/.worktrees/pv-b3p6`, branch
`codex/pv-b3p6-20261028`. Entry `0c43174f5334a5b9b276071808bfd69f5e792a3c`
(requested head 28b8dd3411 is its parent). [Commit log](COMMIT-LOG.txt).
100/100 Lean attempts, IDs63100–63199: 86 pass,14 rejected, all retained.
Zero native scopes, zero Kani, zero admission refusals/void attempts.
The relaunch recovered the already completed audits; no compile was repeated.

**Runjoin's op227 hypothesis is not discharged. Target not yet established.**
No replacement theorem exists for
`R1Z.PV_RunJoin_OracleBridge38.selected_callback`; its exact hypothesis is in
[runjoin-hypothesis.txt](runjoin-hypothesis.txt). Byte-for-byte replacement
checking is therefore not applicable.

Item(a) reused unchanged. Item(b) gained named ordered-loop, emitted-read,
full public-digest read-continuation, and nine individual matrix-store laws.
`value_sequence_read_binding9` binds the 15-stage sequences, but the actual
value-body entry factorization hit default recursion depth and is excluded.
The inventory and those laws do not establish the exhaustive source binding.
No limit was raised. Items(c), D188/direct intermediate matrix, and(d), actual
slice callers/complete pre-inline std source coverage, remain after(b).
[Exact residuals and next proof shape](RESIDUALS.md).

|Audit target|Exit|Wall s|Peak RSS KiB|Swap|
|---|---:|---:|---:|---:|
|63197 Resume9Combined|0|1.090|2670736|0|
|63198 Resume9Axioms|0|1.216|2668572|0|
|63199 Resume9Focused|0|1.079|2670888|0|

Audit source revision `e10892584a0e94ca99c9e8631f76325cf6cc8f23`.
One frozen focused manifest passed; no endpoint replay claimed.
[Verification](verification-summary.json) checks100 source snapshots and their
revision blobs,121 theorem axiom reports,5673 external objects and173 retained
objects. Accepted axioms only propext,Classical.choice,Quot.sound.
All scopes6G/8G/swap0/TasksMax64,Lean-M7000; maximum process RSS2735724KiB.
[Receipts](receipt-index.json).

All Rust interpretation is **reclassification within existing Charon/Aeneas
tool trust**. Own-1 source binding is required; compiler preservation stays
at V370 / pending owner D381,D386, never T. No endpoint/ledger premise removed,
added,weakened or moved into T; simulator/observer unchanged.
V228/V229/V243 retain accepted status; V241/V245 not started.
No Rust/ELF change,push,merge or key deletion. Pinned cache retained.
Stopped at100-attempt budget exhaustion. Next: exhaustive transformed-body
binding and selected callback source/value law, then(c), then(d).
