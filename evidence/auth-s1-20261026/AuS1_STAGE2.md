# Stage 2 — source trace and row-30 read components

Checked roots: AuS1_Trace (019), AuS1_Suffix (020), AuS1_Absorb (026),
AuS1_Observe (027), AuS1_Block (029), AuS1_Frame (037), AuS1_Row30 (041).
Standard three axioms, exit0, swaps0; exact metrics and attempted-source
snapshots in numbered receipts. 040 diagnostic trace is retained; its failure
revealed shadowed identifiers reordered by subst, fixed using unique bind names
in041. No timeout/memory kill in this stage. No package replay.

AuS1_Observe.lower is all-outcome equality of the native lowerer's returning
read observation and complete preparation code's native observation. Failed
attempts remain in the native attempt log. No rejected prefix or duplicate is
removed from the underlying attempt log.

AuS1_Row30.reached inverts the actual source-shaped original preparation with
an opaque child-effects dictionary, exposing row30's scalar call, its SAME
root/bytes1/bytes2 and read inclusion into the same preparation log. It does
not assume scalar success: it derives success from the enclosing successful
preparation. AuS1_Block.scalar_read supplies the actual absorption read for
the concrete hash scalar. AuS1_Frame.folded proves the offset38 root reader
symbolically; it works for every tag and length word, using the fixed 32+2+4
prefix size, without reducing a concrete numeric byte encoder.

Still open: compose these components with actual vector-copy contents,
sourceView folded-root provenance, complete enclosing preparation log, and
joint accepted cuts/recovery. No authenticated_S1 premise removal claimed.
No global experiment/budget work, no other prefix edits, no shipped changes,
no ELF trigger and no key/funds operations. The security target is unchanged.
