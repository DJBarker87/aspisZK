# Stage 1: safe model, native proof pending

Checked NP6_StdModel.reserve_contents, box_contents, returning_nonvacuity and error_contents, and NP6_ClaimsModel.filled_contents, row_clone, row_filled and reference_normalized. All completed audits use only standard axioms. Complete Result normalization of the selected safe reference retains the actual validated record and decoder. The allocator outcome is explicit; successful allocation is not assumed. Generic filled_contents explicitly requires the element clone law, discharged for the actual row copy implementation by row_clone.

No ledger row is removed. These are model laws, not a native dictionary association. L174/L177/L179, the joint top and its quantifiers remain unchanged. No new trust item or cryptographic hypothesis.

L001 passed. L002-L004 are failed elaboration attempts; their sorryAx output is an error artifact and is NOT accepted evidence. L005 passed with standard axioms only. Receipts include source/dependency hashes, target, exit, wall, peak RSS, swap and cgroup settings. Source revision is the pre-edit stage revision; dirty source snapshots are retained in each receipt directory.

K001 whole-Claims comparison was manually stopped on formula-growth review at ~6.4 GiB (exit1,119.136s,6446528 KiB,swap0), before crossing the cap. K002 isolated an arbitrary selected output cell and lowered the per-loop unwind bound to32; it was also stopped near6.4 GiB. K003 splits Result/error equality from contents. None is a counterexample against shipped Rust; stopped jobs are unproved. No unchanged retry or cap increase.

The separate proof crate contains the exact complete shipped Claims body, complete shipped wire and sampler modules, and the selected extracted safe reference. Only a cfg(kani) prefix constructor and forwarding wrappers are added there. No stubs. No shipped file under crates/ or programs/ is edited, so no ELF rebuild trigger has fired. Existing ELF pins are inherited, not reproduced. The 87 core Rust sources match the retained host snapshot exactly.
