# Candidate helper computes original S2 coefficients

PROVED: `candidate_top_success_has_original_coefficients` starts with the actual successful generated-candidate helper call and explicit canonical-read conditions, and derives all four original S2 coefficient equations for its same mapped output. The q0/q1 witnesses are tied to that candidate execution's actual extra[0]/extra[1] reads. It reuses the existing S2 original/factored identity and the newly checked selected-helper composition.

PROVED: `candidate_top_success_maps_to_p6` constructs the earlier suffix-transport premise from the actual same-call continuation; no suffix-equivalence or desired-output-equation premise remains. The canonicality corollary proves all four mapped output cells canonical under the same input contract, reusing the public mapped-read inverse theorem. See BEFORE-AFTER.md for the exact scope of premise removal.

RETAINED: actual successful candidate execution, canonical mapped-ap0 reads, canonical mapped-ap1 reads, and canonical mapped extra challenge values. These input facts must be supplied by the caller/parser. This is an accepted-run helper result, not an all-input termination theorem.

OPEN: complete frozen Rust/library/caller provenance, required totality/range release obligations, candidate adoption, final source/artifact binding, S10/coherent replay and the composed 100-bit soundness theorem. No full S9 release-cone closure or security target is claimed. Production source unchanged.

Focused checks: Lean 4.32 -j1 -M4400, atomic mutex/RSS watchdog, standard axioms only; exact source/import/tool hashes, revision/status/time/RSS/observed swaps retained. No proof-limit overrides or compiled objects. V3 controller excludes exact metadata-only --print-prefix/--version queries while retaining actual compiler exclusion. Warm-cache checks are not coherent release replay. Run `python3 -B check_packet.py` for evidence validation without compilation.

Source scope: this packet applies specifically to the retained-four-multiply attempt-2 candidate weights SHA `9338607afd636f43b3b830bbf9cf3cc0ced1fa7cc78b266282969e519577bccf`. It does not apply to the separate source-only 9ce draft or the unchanged production helper. See SOURCE-PIN.md.
