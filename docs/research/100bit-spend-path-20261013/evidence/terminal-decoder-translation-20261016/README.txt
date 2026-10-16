Decoder translation and native differential evidence, 2026-10-16

Candidate source: 72a288c2cf7745c27d1777159215116c22a63f91.
Compared with reviewed production42e5, this candidate expands three fixed loops
in ascending order (eight digest limbs and two twenty-node frontiers), expands
two reserved-byte any predicates into ordered short-circuit comparisons, and
uses seven explicit bounded full-array slices for byte comparisons. The
previous guards, first-error order and returned field order are preserved by
source review; no universal Rust equivalence theorem is claimed.

Retained attempts: owned-array assignment still fails Aeneas context joining.
Literal expansion passes the loop translation, then exposes four enum-name
collisions. The recorded metadata adapter changes exactly four constructor
rename fields, and its inverse recovers the complete original LLBC JSON.
Full-slice syntax translates but introduces reachable RangeFull externals.
Explicit bounded ranges remove those externals. The final unused Slice.eq
template is retained unchanged; there are zero references to it in Funs.

Final Charon: exit0,76.380s,661160KiB peak process RSS,zero swaps.
Final Aeneas: exit0,21.608s,3863552KiB RSS,zero swaps.
Every invocation ran with MemoryHigh6GiB/MemoryMax8GiB/MemorySwapMax0.
Tool binaries, source pins, raw LLBC, adapted LLBC, generated originals,
failed logs and all resource receipts are retained. No downgrade or opaque
implementation was used. Translation success is not a Lean closure claim;
actual decoder axiom checks, including unwrap/Formatter dependencies, are OPEN.

The optimized native build passed in114.305s,548284KiB RSS. The complete
20,720-case trace is byte-identical to the retained original decoder trace:
66,622,110bytes, SHA256
628a3418096f93d769955ff18e7ac2f4e8fcb25b659b66aac3360204ad94efff.
The corpus includes both ASF8 variants and component decoders, all length cuts,
single-byte0/255 changes and paired header/body changes. It is finite evidence.

verify.py independently checks175 archive members,3028 Git source pins,
the reversible name adapter, eleven translation/native receipts and four
regression receipts, including the reused baseline. No proof replay is run.
Its initial working-directory tree lookup and temporary-output reuse defects
were corrected before the recorded successful verification; neither affected
the retained compilation, translation or runtime jobs.
