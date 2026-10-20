# Delayed base-dot reduction: bounded batches and actual finishing reducer

The source-shaped mathematical batch model proves each group of at most four canonical M31-limb products fits u64. Seven separately folded groups sum below 2^37 and preserve the exact residue of the unreduced sum. Applying the retained proved M31.reduce_u64 implementation returns that sum's canonical residue. The fold and reducer facts reuse the existing rho arithmetic and pinned NUC reducer cache.

This closes candidate4's mathematical batch-size/residue obligation. It does not prove array/slice decoding, actual Rust loop-to-batch correspondence, WideExact coordinate mapping, or the three tail terms. Product caps and batch shape are explicit; no canonicality claim is made for arbitrary raw tuple values. The exact current fast_dots.rs snapshot is pinned for subsequent extraction.

Final focused Lean 4.32 check: exit 0, 2.12 seconds, peak RSS 2,250,932,224 bytes, zero process swaps; four reports contain only standard axioms. The failed predecessor used looping add_mod simplification; a structured three-step modular equality replaced it without raising limits. Complete commands, revisions, source/object/import hashes and raw logs are retained. Cached working evidence only; no unified release compile or full verifier refinement is claimed.
