# Strengthened selected projection dot step

This packet proves `continued_projection_dot_step_at` for the actual emitted projection loop body. Its hypothesis pins the same `Range.next` result to `some j`; the body result then yields the same-index accumulator read, actual `weights.field` success, same-index coefficient read, product, update, and return. The actual field reader establishes field-value canonicality, and the selected arithmetic semantics establish canonical total plus `decode total = decode old + decode value * decode coef`.

Canonicality of the accumulator and coefficient reads remains an explicit contract. The theorem is only a one-step source-cut result; the four-iteration projection-loop decomposition and caller composition are not claimed by this packet.

The packet retains exact focused Lean 4.32 source, import profile, command, preflight, receipt, log and concurrency observations. It includes no compiled objects.
