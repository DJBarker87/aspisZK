# Selected helper computes the original S2 coefficients

PROVED: `two_body_output_factored` derives all four factored coefficients from the same successful selected-model two-body execution and its shared arrays/challenges. `successful_selected_helper_has_original_coefficients` lifts this to the actual successful selected P6 helper loop and reuses the existing `S2LibraFactoredIdentity.original_eq_factored` identity. The challenge witnesses are tied to the same execution's successful `extra[0]` and `extra[1]` reads.

RETAINED: successful selected helper-loop execution, the explicit canonical-read premises for ap0/ap1/extra, and the selected concrete P6/source-model boundary. No independent scalar/sum/power/output equation is assumed. Reusing the shared witness does not discharge caller/source hypotheses.

OPEN: complete candidate-to-helper transport, candidate adoption and Rust library/caller provenance, final frozen artifacts, S10/coherent replay and the composed 100-bit theorem. This selected-model result does not establish full S9 closure or the security target. Production source unchanged.

Focused checks: Lean 4.32 -j1 -M4400 under atomic mutex/RSS watchdog; exact revision, source/import/compiler hashes, status, time, RSS, observed swaps and standard axiom audits retained. No proof-limit overrides or compiled objects. Warm dependency checks are not a coherent release replay. The V3 controller ignores exact metadata-only --print-prefix/--version commands while retaining actual compiler exclusion. Run `python3 -B check_packet.py` for retained-evidence validation without compilation.
