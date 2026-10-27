# Complete byte decoder carrier transport

XSe_ByteDecoder.source: for EVERY s : Slice U8,
XSc_RecordByteLength.mapped s = aspis_core.field.wide_exact.WideExact.from_le_bytes s.
No validity, canonicality, successful-call or length hypothesis. It includes length rejection and all eight little-endian words on length32, via XSe_ByteWindows.index/window, XSe_OldBytes.source and XSe_KitBytes.source. Reuses XSc word and limb decoder theorems unchanged. No sampler re-proof.

L009 passes (standard axioms only), 1.075982864s, peak2654052KiB,swap0. L003/L006/L008 establish predecessors. Full per-attempt commands, source/dependency hashes, revision, limits, exit, timings and axioms in receipt directories. Failed L002/L004/L005/L007 prints excluded. No memory kill or timeout. Budget9/100 Lean,0/10 Kani.

A8 remains OPEN: full validator-window/first-error loop equation, installed verification and chronological attempted trace transport. Actual-top premise delta0; adopted83T/0P/13G unchanged. No new trust, cohort weakening or shipped source change.
