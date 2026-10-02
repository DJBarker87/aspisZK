# Checksum coverage review (2026-10-02)

The previous verifier and checksum/inventory indexes are preserved under `pre-review-checksum-fix/`. The package verifier now excludes only its own top-level `SHA256SUMS` from the package file set; nested checksum files remain included and verified as package artifacts. The inventory excludes only itself and the root checksum index. The R363/R364 package was re-indexed without changing the underlying translation, build, or proof evidence. No Lean or Aeneas tool was run in this review.
