# NJY failing step

K041 checkpoint broad step TIMEOUT: CBMC timed out at90s; scope98.411754637s, peak1,458,372KiB, swap0. No credit; K042 control skipped. Formula combined dynamic offset112+8*lane across192 bytes, eight-byte decode, array update/frame and capacity rejection in one full Result contract. It was never rerun unchanged and neither timeout nor cap was increased.

Replacement: separate eight-byte source loop_window (arbitrary lane<8) from the one native update/capacity step on that exact eight-byte window. The latter factors the local start to0, keeps arbitrary pre-state and full array frame, and retains the rejecting branch. NJQ_Words/NJI_CheckpointLoop window and frame/finite-induction laws compose them. Master's unlaunched step is changed proactively to the same split. K041 remains in receipts and budget accounting; successful compilation or other failed controls do not relabel its timeout.

Validation repair: NJY_validate.py now explicitly classifies 'CBMC timed out' as non-semantic failure even when Kani also prints VERIFICATION:- FAILED. This is stricter than the initial classification. The timeout is a retained finding, not a matched control.

L006 focused window lemma compile failed on an opaque Usize literal in an omega bound, before any combined audit. Its error recovery printed sorryAx; this failed output is excluded. Source repair makes the eight-byte size explicit with change before omega; new attempt L015 must pass with standard axioms. No failed theorem or object is accepted.
