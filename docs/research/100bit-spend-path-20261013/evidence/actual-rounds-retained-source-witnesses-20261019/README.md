# Actual rounds retain decoder and reached-call evidence

Successful RoundModel.rounds with the actual decoder and polynomial operation boundaries now yields an enriched ordered trace. Each step retains the original checked source step, the actual record and successful decodeMain call for its coefficients, its reached semantic call and challenge, exact alpha update, polynomial recurrence and degree bound. Existing source reachability also supplies the ordered SemanticRun and equality of its challenge list to the returned alpha array.

This repairs an overly strong unpublished bridge that quantified polynomial/challenge agreement over hypothetical calls. No such universal callback premise is present here. The actual run's polynomials still need to be connected to the same accepted typed payload view, challenges to the corresponding transcript view, and initial/final values to maskSum/terminalZ. A subsequent annotated-list theorem must retain the entry-to-source relation; a separate Run conjunct alone is insufficient.

Lean 4.32 exited 0 in 8.81 seconds, peak RSS 3,284,090,880 bytes, zero process swaps; both theorem reports use standard axioms only. Exact sources, import owners, object hashes, command, revision and logs are retained. This is focused working evidence, not complete soundness or a unified release replay.
