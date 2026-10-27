# Complete external-layer P6 gate

Target poseidon2::builder_reference::pv_runjoin12_external::external_all_words passed, without stubs or input assumptions, for arbitrary `[u32;16]` states. The source external_linear_lazy mutates actual; the existing owned external_owned computes expected, and all16 output words are compared.

Exit0, wall129.3816s, peak RSS816414720 bytes, swap0. Complete raw log, controls and exact source pins are in pv12-runjoin-kani-11 and kani-invocations.jsonl. The source poseidon2.rs hash is4563a7192a69748ab0a56ddc023a9f13f2d96d0064cd829dd17ac358bce1a740. The existing extraction is reused from BuilderPoseidonExtracted, with the receipt in builder-cont3 evidence; no duplicate extraction.

This link is P6, not a Lean theorem and not a trace/side-channel claim. The E_shipped adapter compiled at40905: exit0, wall0.96s, peak2654236672 RSS bytes, swap0; its equation identifies the reused extraction and has only the standard three axioms. Records association, compiler-return, transition equality, deployed public binding and deployed non-vacuity remain open. T is unchanged.
