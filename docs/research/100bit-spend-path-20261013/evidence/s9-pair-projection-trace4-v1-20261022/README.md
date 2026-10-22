# Four-step projection-loop trace extraction

The theorem starts from successful execution of the actual emitted `pair_s2_libra_parts_projection_loop` over the concrete range `[0,4)`. It derives all four continued body calls from the loop result, with exact `Range.next` indices 0, 1, 2, and 3, the same intermediate arrays, and the terminal state at range end 4. The five per-range next equations are proved from the pinned range specification.

This packet proves loop decomposition only. It does not assert dot semantics, coefficient or accumulator canonicality, or a complete caller/security theorem. The exact source, command, profile, receipt, log, concurrency evidence and standard-axiom audit are retained; compiled objects are excluded.
