# Stage 1: total cohort byte decoder

Established `XRv_FromFnTotal.loop/total` (L002) and `XRv_DecoderTotal.ranks/map_stable/decoder` (L005). For EVERY `block : Array U8 32#usize`, decoder proves `∃ out, AspisR1QueryScanUnrolled.r0_transcript.query_words block = ok out`. This covers all typed blocks without caller success, canonicality, or arithmetic premise. Failure/divergence are impossible in this decoder; driver/digest error paths remain separate obligations. Generic constructor callbacks must be stable and total; the concrete ranks instantiates that condition with the inherited checked four-read theorem. No inherited result re-proved.

Before: XRt_QueryWords.same_words needed successful decoder output as a hypothesis. After: decoder success is unconditional, so that hypothesis can be derived. Exact eight-word equality will be composed after restoring XRt objects. The whole transcript.queries equality and whole A2 remain OPEN. A3 not started. A0-A8 each OPEN; adopted headline unchanged, zero premises removed and T0/P0/G0/C0 ledger delta (atomic-family/SAME-witness/shared-nonce/L185=L159 method). No quantified carrier, failure event, game or trust change.

Five compile attempts: L001,L003,L004 failed (excluded); L002,L005 pass. Source fixes replace unresolved dependent matches / alias conversions, with no timeout or memory pressure. L002 exit0 wall1.468390731s RSS2649908KiB swap0; L005 exit0 wall1.180891814s RSS2634980KiB swap0. Full source revision/hash, dependency/tool fingerprints, limits, stdout and axioms are in each receipt. Every new theorem prints only standard axioms or a subset. No Kani/Rust/shipped source/ELF change.

Non-vacuity: block carrier inhabited by Array.repeat32 0; theorem universally constructs a successful output, rather than assuming one. This supplies no joint accepted deployed execution.

Next: SAME decoded words, full SAME-array blocks/advances driver and selected state, then eager transcript continuations. Root statement audit will reuse replay cache.
