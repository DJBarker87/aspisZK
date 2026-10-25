# Local-call obstruction witnesses

RowShape_SlotObstruction.shape_success_not_parser: an admissible supplied Ops
record, passed through the EXACT existing Claims installation, returns Ok S1 on
empty bytes while frozen parseReached returns none for every transcript.
scan_success_not_canonical: the installed op4 returns Ok () on a symbolic
7031-byte zero prefix followed by the four bytes ff ff ff ff; the first frozen
scan word is 4294967295, exceeding 2147483647. Padding is handled symbolically,
never by kernel expansion of thousands of list cells.

These are LOCAL CALL witnesses. They do not assert malformed whole-transaction
acceptance, refute a future accepted-run interpretation, or invalidate a source
implementation. They show that the installed dictionary's free slots do not
supply the desired concrete body laws. Adding parser/scan-success hypotheses or
silently replacing Ops would not discharge that source-instance obligation.

Attempt RowShape-003 failed at Option bind simplification, opaque Usize.max and
broad simp expanding replicate (recursion-depth limit). No memory kill or wall
timeout. RowShape-004 fixes Option reduction, uses scalar_tac for the small bound
and symbolic drop_replicate for padding. Exit 0, wall 2.375994873989839 s,
peak RSS 5347464 KiB, swaps 0; every printed theorem uses only propext,
Classical.choice, Quot.sound. Diagnostic sorryAx in failed003 is excluded.
Full source hashes, dependency fingerprint, command, limits and revision
42f96602a3 are retained in receipts. Budget 4/100 Lean, 0/60 Kani.

Shipped source inspection: crates/aspis-r1-cost-probe/src/candidate.rs:40
parse_shape checks ONLY length/magic/tag/zero tail and returns S2.
canonical_scan at :54 checks all nonsemantic regions and all22 openings;
semantic Prefix::parse is a later call after expansion. Frozen parse combines
header, complete scan and semanticRows, then parseReached adds transcript
alignment. These stages require a contextual ordered-call composition, not
identifying the header-only body with the combined parser on arbitrary inputs.
The retained Stage2ParseShapeSuccess proves S2 on its own explicit extraction
and supplied trait operations; it does not install that body in Claims Ops.

No release claim, premise discharge or new trust item. S2 remains open. Next
check: exact authenticated-TX2 installation projection, then report missing
concrete native source/ROM bindings rather than claim either requested row closed.
