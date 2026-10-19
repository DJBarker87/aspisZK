# Main field owner adapter and checked-run polynomial equations

The structural QM31 adapter is coordinate-invertible and transports canonicality between the PublicPreparation record owner and the selected exact field.rs extraction. It maps add/mul and the actual 28-field boundary/reverse-Horner fold shapes through the reused operation proofs. A concrete RoundModel.Boundaries constructor uses these mapped boundary/value functions and a caller-supplied record decoder.

RawSemanticCheckedStepPolynomialAdapter derives p(0)+p(1)=the prior running value and the next running value=p(challenge) from a successful checked step under that constructor. RawSemanticCheckedRunPolynomialAdapter lifts this over the checked run, retaining the per-step decoded row/challenge and alpha update witnesses. It requires explicit universal canonicality of successful record/challenge decodes and a successful updated-round array index.

Source linkage remains explicit: field.rs is byte-identical to the retained arithmetic extraction (SHA256 28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea), but the generated PublicPreparation owner does not emit add/mul/decode_k bodies. A record isomorphism does not establish those absent call bodies. No production RoundModel operation/decoder refinement, initial row14 maskSum equality or final terminalZ correspondence is claimed here.

All three focused Lean 4.32 checks exited 0; times 6.18, 3.97 and 4.5 seconds; maximum RSS 2,531,655,680, 2,553,397,248 and 2,541,387,776 bytes; zero process swaps. The coordinate inverse/canonicality reports are axiom-free; remaining reports contain only standard axioms. Exact commands, source revisions, source/object/import hashes, raw logs and compiled objects are retained. Historical versions in the original worker packet are diagnostics/provenance, not the selected objects.

These cached checks are working component evidence. Concrete accepted-source/decoder/operation refinement and a clean unified ordered build remain open. This is not the complete 100-bit private-spend theorem.

The new degree bridge proves each retained 28-coefficient polynomial has degree at most 27. The checked-run Sumcheck adapter carries those witnesses through the actual ten-event schedule, preserving initial boundary and final challenge-evaluation projections. Those endpoints are decoded running claims; identifying them with maskSum and terminalZ remains open. Both new focused checks pass with standard axioms only. Full metrics are in the receipts.
