# R196 selected byte writer bridge

R196 applies the completed generic 16-byte serialization theorem to the actual selected field writer. It proves the selected CM31 and QM31 writers equal the earlier proved writer under a limb-preserving type conversion for arbitrary values and output slices, including every error. For a 16-byte output slice, the exact little-endian limb bytes follow from R144; no canonicality premise is needed.

The new bridge compiled in the pinned capped Lean 4.32 cache: exit 0, 1.09 seconds, peak RSS 2,541,732 KiB, zero swaps. All three complete axiom reports contain only the standard foundations. The [evidence](evidence/r196-current-byte-writer/manifest.json) records the exact compile revision and source checksum. The unchanged generic serializer checks were not rerun.

Next: connect the current callback’s complete `bytes_loop` and `bytes` declarations to the existing generic serializer, then vector header extension and the remaining selected fold operations. Whole callback trace equality, privacy and soundness remain open. Verifier source, CU results and all parameters are unchanged.
