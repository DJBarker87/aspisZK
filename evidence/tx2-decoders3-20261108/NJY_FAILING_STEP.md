# NJY failing step

K041 checkpoint broad step TIMEOUT: CBMC timed out at90s; scope98.411754637s, peak1,458,372KiB, swap0. No credit; K042 control skipped. Formula combined dynamic offset112+8*lane across192 bytes, eight-byte decode, array update/frame and capacity rejection in one full Result contract. It was never rerun unchanged and neither timeout nor cap was increased.

Replacement: separate eight-byte source loop_window (arbitrary lane<8) from the one native update/capacity step on that exact eight-byte window. The latter factors the local start to0, keeps arbitrary pre-state and full array frame, and retains the rejecting branch. NJQ_Words/NJI_CheckpointLoop window and frame/finite-induction laws compose them. Master's unlaunched step is changed proactively to the same split. K041 remains in receipts and budget accounting; successful compilation or other failed controls do not relabel its timeout.

Validation repair: NJY_validate.py now explicitly classifies 'CBMC timed out' as non-semantic failure even when Kani also prints VERIFICATION:- FAILED. This is stricter than the initial classification. The timeout is a retained finding, not a matched control.

L006 focused window lemma compile failed on an opaque Usize literal in an omega bound, before any combined audit. Its error recovery printed sorryAx; this failed output is excluded. Source repair makes the eight-byte size explicit with change before omega; new attempt L015 must pass with standard axioms. No failed theorem or object is accepted.

L007 focused roots compile failed because rewrite does not unfold the new model abbreviations. Replaced those four proof scripts with direct Eq.trans of the same source and reference=model equations; statements unchanged. L016 is the new current-source attempt. L007 error-recovery sorryAx is excluded. No combined gate had launched.

NJY-B1, L017: actual slot type check rejects raw master/checkpoint functions at48/49. Their complete Rust Results use PoolV1PairForestAccountErrorV1; those adapter slots implement decode_master_box/decode_checkpoint_box with ProgramError and Box (erased carrier). This is a slice boundary, not a reason to change a model/carrier or add an equality hypothesis. Direct installation48/49 is STOPPED and excluded; no wrapper/native credit is claimed. L018 installs only direct registry31/entry32 and proves digest/error43/44 and wrapper48/49 frames. The five assigned raw decoder rows still have their complete native/reference/model/carrier packets; wrapper consumers must instantiate/map them in a separate owned row.
