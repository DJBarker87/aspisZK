# Ordinary sampler callback canonicality

This packet records the focused Lean proof for the ordinary sampler callback and Prepared row-28 `kappa` canonicality specialization. The callback computes `sampler.ordinary_sample` and maps its output to the Prepared carrier. The proof derives the successful output bounds from the checked sampler/carrier owners, then obtains the actual row-28 successful scalar call from `prepare_success`; `tail_concrete_run` identifies that value with the returned `out.kappa`.

The result is a source-model proof. Production adoption, runtime equivalence, sampler totality, and distribution properties remain open. Gamma is covered by its separate packet.

The accepted run is `attempt/proof-evidence/receipt.json`; its log contains the three `#print axioms` audits, all standard-only. The exact accepted source and pinned dependency sources are included in `sources/`; producer receipts and dependency closure are referenced in `manifest.json`. Failed preflight/proof attempts v1–v8 are retained under `diagnostics/` and are not accepted results.
