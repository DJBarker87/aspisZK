# Batch aggregation obstruction

The three native tree adapters are checked separately. RootReads root0/root1/
folded are checked in attempt009. 007 hit Lean memory threshold while importing/
checking the attempted batch composition (exit134,4.147439s,7171892KiB,swap0).
The source was split: 008 diagnosed the folded equality without reducing proof
bytes; 009 uses JGc_TX2_M2Root.selected_root and encoded_root and passes.
010 replaced batch root reductions by those certificates and still hit the
threshold (exit134,4.113460s,7171832KiB,swap0). 011 isolates only the three
imports and #check calls; it also fails during import before any output,
exit134,4.185s,7169976KiB,swap0. See exact receipt metrics.

This is an import-closure resource obstruction, not a real-byte vacuity finding.
No cap raised or unchanged failure rerun. The failed composition, dependent
prebatch and import-only diagnostic are retained as unchecked text. No full
native batch or accepted1 credit is claimed. Continue independent TX1 query
sources. Host infrastructure/cache repair is outside the authorized proof job.
Budget 11/100 Lean launches,0/10 Kani. Full FJv counts unchanged83T/3P/13G.
