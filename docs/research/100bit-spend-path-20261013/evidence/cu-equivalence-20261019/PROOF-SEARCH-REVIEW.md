The first combined base-loop draft used an unbounded repeat of all_bind.
This proof-search shape can continue introducing metavariable binds after
reaching the final constructor. The verified own Lean PID was stopped with
SIGTERM after peak RSS 8614952 KiB, wall 107.334 s, zero swaps. Its exit is143,
not a proof result. No cap was raised and no unchanged rerun occurred. The
replacement isolates source body equality, explicitly inverts the thirteen
actual binds, proves iterator progress, then consumes the generic checked loop
relation. All three focused replacements pass below 2.6 GiB and 2.9 seconds.

The slot transport draft used a broad pair-match rewrite under arbitrary
continuations. It was stopped after 49.516 s, peak RSS 3119244 KiB, zero swaps,
exit143. The replacement first checks both actual emitted callbacks equal a
common continuation form, then explicitly traverses its eighteen binds and
reduces the one known mutation-result pair. cu-dots-slot-f passes in 1.804 s
at 2629532 KiB, zero swaps. No generated declaration body was edited.

Later focused 100000-heartbeat failures exposed an elaborator heuristic
comparing the unselected branches of equal let/match expressions. Explicitly
changing the known none branch to its done constructor prevents arithmetic or
loop unfolding in that branch. This is a symbolic control-flow fact; it does
not enlarge memory or timeout caps. Tail and batch comparisons then pass.

All stopped/failed drafts and commands are retained; only successful exact
current-source receipts enter COMPONENT-AUDIT. PROOF-SEARCH-REVIEW.json links
resource data and source revisions. Per-target #print axioms is in each run;
failed or interrupted output is never counted as a theorem result.
