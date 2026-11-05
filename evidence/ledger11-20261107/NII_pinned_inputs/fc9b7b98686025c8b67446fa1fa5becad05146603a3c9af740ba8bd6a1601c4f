# NHA reproduction

Pinned tool binary Aeneas SHA256 c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958 (XRa extended b59d5188). Charon SHA256 daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8. No Charon rerun for these retained LLBC reproductions. Exact input hashes and origins: NHA_INPUT_PINS.json. Exact commands, source revisions, limits, wall/RSS/swap: NHA_E001..003/receipt.json.

| Attempt | Shape / actual provenance | Exit | Wall s | RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| NHA_E001 | NGA reference accumulate/small: nested loop, arrays of arrays | 2 | 0.340204 | 69520 | 0 |
| NHA_E002 | frozen queries_from_pairs: block loop with early break, fallible finish | 2 | 0.355571 | 71808 | 0 |
| NHA_E003 | frozen prepared_claim: nested points/lanes, borrowed matrix selection, early Result return | 2 | 0.366188 | 71456 | 0 |

All three fail in symbolic loop interpretation/join/collapse/borrow handling, before backend Lean emission. Field: InterpBorrows.ml:2731 rejects a non-PNone shared-loan projection marker during dummy/abstraction simplification. Queries and claim: InterpReduceCollapse.ml:1991 does total Map.find on an abstraction absent from nabs_map when replaying shared borrows after merges. Neither error refutes the Rust function or a model theorem.

## Provenance finding NHA-F1

The job description calls NGA E001/E002 an actual-frozen-body extraction. The committed NGA_extract.py, NGA_reference.rs.txt and retained LLBC instead target crate::accumulate and crate::small, using transparent u32 cached words and a step helper. E001/E002 also have different reference hashes. NHA_E001 reproduces the retained final LLBC (84990a63...), not a nonexistent retained actual-field LLBC. The frozen field body is separately preserved byte-for-byte in NHA_qm31_accumulate_product_channels.rs.txt. Success on the reference would not establish actual frozen extraction.

## Setup exclusions

S001 failed while copying dangling source/doc symlinks; S002 encountered a read-only copied executable. Own setup fixed to ignore dangling symlinks and hash-check existing copies. S003 succeeded, 91 MB private directory. No Aeneas extraction ran during either setup failure. Shared install and infrastructure unchanged.

No theorem added; #print axioms N/A. No patched tool or closure credit. All runs admitted with exit0 AND allowed:true and exact 6G/8G/swap0/tasks64 limits.

## Actual frozen field reproduction

NHA_C006 successfully extracted the full byte-identical frozen field body in a renamed public scratch wrapper, with exact frozen QM31/CM31/M31 types and opaque field-add callees. Its LLBC is committed and pinned by NHA_C006-pins.json. NHA_E007 runs that LLBC and reproduces the SAME InterpBorrows.ml:2731 assertion inside the actual inner channel loop (scratch lines20..23). Thus NHA-F1 does not prevent confirming the actual frozen obstruction; it corrects what the earlier retained LLBC established. No actual body statement is inferred solely from the reference.
