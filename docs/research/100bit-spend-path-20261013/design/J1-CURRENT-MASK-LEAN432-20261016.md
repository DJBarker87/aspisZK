# Current mask arithmetic passes on Lean 4.32

The selected-mask arithmetic and prepared-multiplier components now pass on
one Lean 4.32 kernel, satisfying the toolchain requirement for these components
in [J1.R17](LEAD-REVIEW-J1-R11-R12-20261015.md). The NUC's pinned library cache
was reused after a no-build freshness check; six historical pure proofs and
fourteen maintained extracted-operation proofs were reused unchanged. Two new
scalar-operation proofs connect the actual extracted multiplication to the
exact field embedding.

The [evidence](../evidence/current-mask-lean432-20261016/README.md) records
24 successful focused targets, 75 standard-only or axiom-free reports,
2,987,088 KiB maximum target RSS and zero process swaps. Every target ran alone
under a 6 GiB cap with swap disabled. Exact snapshots, object/import pins,
resource logs and independent audit are retained. A missing Mathlib import
was resolved by selecting the complete cache at the same pinned revision;
the rejected paths and corrected run are recorded. No full manifest replay
or runtime/artifact test was repeated.

Generated function bodies are unchanged. Only broad imports were narrowed to
the matching Aeneas runtime plus the loop-attribute module; reversing those
edits recovers the original extraction bytes exactly. No 4.31 objects were
used in this workspace. This does not prove the extractor/compiler correct.

An earlier helper inventory incorrectly omitted negation from the mask call
cone. The generated `cm31_mul_i` calls `M31.neg`, and tower-basis branches 1 and
3 call `cm31_mul_i`. A canonical-input negation proof is therefore required.
The old inventory remains historical evidence; this paragraph corrects it.

The complete selected-mask function and actual verifier acceptance contract
remain open. The next source obligations are coefficient-array population,
selected linear forms, basis decoding, Horner-to-polynomial composition and
the explicit power/mask term. The broader transcript, sampler, commitment,
knowledge-extraction, privacy and runtime/settlement gates remain as recorded
in the status report. No complete 100-bit claim is made.
