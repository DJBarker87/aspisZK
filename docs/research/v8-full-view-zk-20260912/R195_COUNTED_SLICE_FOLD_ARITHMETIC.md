# R195 counted-fold index bounds

For any representable `usize` index smaller than a representable length, R195 proves that adding one cannot overflow. The pinned checked addition succeeds with value `i + 1`, remains at most the length, and remains below the length whenever the next word differs from it. The result applies even at the largest representable length.

The focused target compiled in the pinned capped Lean 4.32 cache: exit 0, 1.18 seconds, peak RSS 2,533,564 KiB, zero swaps. Both complete axiom reports contain only the standard foundations. The [evidence](evidence/r195-counted-slice-fold-arithmetic/manifest.json) retains exact source, launcher, logs and rejected drafts.

The source uses `unchecked_add`; R195 supplies its no-overflow condition and proves the checked-operation result. It does not establish the unchecked operation’s source correspondence, pointer reads, length/empty tests, or the actual selected fold. Whole callback chronology, privacy and soundness remain open. No verifier source, parameter, CU evidence or unchanged regression changed.
