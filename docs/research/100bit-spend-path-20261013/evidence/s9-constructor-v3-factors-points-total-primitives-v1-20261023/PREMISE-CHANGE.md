# Input scope and premise change

The final proved statement is `AspisR1S9ConstructorV3FactorsCanonicalV1.constructor_success_factors_and_points_canonical`. It quantifies over an arbitrary V3 variant, ten-field alpha, two circle points z, and returned record w. Its complete inputs are:

- `VectorCanonical alpha`: every successful alpha read has canonical QM31 coordinates;
- `PointsCanonical z`: every successful z read has canonical x and y coordinates;
- `weights_new variant alpha z = .ok (.Ok w)`: success of this exact generated V3 source call.

Its conclusion is `FactorsCanonical w.factors ∧ StatementPointsCanonical w.points`. These are universal successful-read contracts on the returned arrays. There is no bit-valuedness premise on alpha and no independent canonical-statement-points or successful-child-call premise.

Before composition, the phase theorem `statement_outer_loop_success_canonical` required both canonical points and canonical initial factors, plus success of that phase. The new whole constructor theorem does not assume those phase inputs hold: it derives the point producer and both factor-phase successes from the same constructor success; obtains canonical points from `statement_points_success_canonical`; obtains initial-factor canonicality from the repeated-zero matrix theorem; and applies the checked phase results. The whole constructor success premise is retained, not proved universally.

The point-producer theorem derives its carry-loop success and both complement subtractions/writes from the same producer success. The loop output canonicality follows from its own same-run arithmetic and exact array updates. Its iteration progress uses the separately checked reverse-range lemma reused from R306. It does not assume that the successor output is canonical.

The seven primitive-totality results have a different scope: on canonical inputs, they conclude existence of an actual successful canonical output for V3 QM31 multiplication and M31/CM31/QM31 addition and subtraction. They have no assumed successful-call premise. QM multiplication reflects success through the complete Result map to the already-proved cut totality theorem, explicitly excluding fail/diverge. Add/sub reuse primitive cut equalities and the actual emitted bind structure. These results discharge primitive arithmetic success existence only.

No premise was replaced with a structure hiding the desired result. The generated V3 source carrier and canonicality predicates were retained. Complete statements and definitions are included in `sources/` and `source-model/`; compiled theorem axioms are recorded in each target log and manifest.
