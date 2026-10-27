# Native expansion stage

LPn_K001 PASS: one native16→32 expansion, arbitrary source/pre-bytes, aligned offset0/32/64 in96-byte backing, variable end and arbitrary observed byte. Actual expand_values executes one iteration, writes low16/copies and high16/zeroes, retains pointer, preserves before/after byte classes.258 properties,0 failed,5 unreachable;22.094819264s,1,015,476KiB,swap0.
LPn_K002 PASS: exact source scalar guard on all n<=1856,m<=3712, matching aligned counts and116-row bound.13 properties,0 failed;2.141715211s,344,920KiB,swap0. It is a scalar association gate, not a call of the complete variable-size function.

Both fresh reservation JSON allowed=true with exit0. Optimized offline Kani0.67.0; frozen graph441 packages, no new tuples/edges; frozen lock5782e6a3… unchanged after each run. No stubs or field multiplication. Exact argv, source/tool/dependency hashes, wall/RSS/swap and compiler diagnostics are in receipts. Inherited LPl_K012 supplies all actual global iterator/window pointers, not the new small backing harness alone.

Scratch begins with unchanged final LPl source (frozen then ordered LPa/LPc/LPg/LPh/LPl); LPn_harness.patch is only the final incremental cfg(kani) instrumentation. Own script adaptation repairs inherited hardcoded prefix/path and selects read-only unchanged LPl modules for private recompilation; no shared launcher/admission code changed. Rust harness source is committed only as patches and receipt snapshots, not an extra Rust source tree.
