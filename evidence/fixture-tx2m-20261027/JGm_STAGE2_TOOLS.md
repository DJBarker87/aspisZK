# Symbolic native control tools

Checked: ReadCell (004), BinarySelect (006), AnyFalse (009), View (010),
Scalar (015), Supplied (016), RowControl (020), PaddingScan (021),
ExternalRun (022). Each has standard-only axioms and an exact-source receipt.
The native padding scan now returns false for any actual chunks_exact return
on each retained zero tail. Its per-word predicate and full any loop are derived
symbolically. The chunks constructor/terminal slot composition is next.
Scratch-prefix reads/writes, supplied-prefix 32-byte reads, occupied/external
input selection, cursor arithmetic and Row.Next/level recursion are isolated;
none takes successful slot/batch/finish/wrapper acceptance as a hypothesis.

Rejected source attempts 005/007/008/011/012/013/014/017/018/019 are retained;
none is a timeout or memory kill. No proof credit is assigned to recovery
sorryAx output from rejected versions. New level drafts are NOT checked yet
and are deliberately excluded from this stage commit.
