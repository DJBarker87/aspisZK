# NFB multiplication abstraction table

No variable field multiplication is evaluated by a credited NFB Kani harness.
NFB_K012 is an excluded timeout of the unsplit root, not an arithmetic pass.
All credited logs and oracles are local mutable records; no function-pointer
comparison, Option<fn> property, writable static or stub_verified is used.

| Native abstraction | Paired emitted Lean law | Domain and caller discharge |
|---|---|---|
| `NFB_row_product(a,b,reply,log)` (opaque local call-log, returns the logged reply unchanged) | `NFB_MulDischarge.multiplication`, L014: emitted `NEW_GeometryActual.aspis_core.field.M31.mul a b = ok reply`, `reply.val=(a.val*b.val)%2147483647`, canonical reply | EVERY raw U32 operand pair. No operand-domain premise. Its canonical reply discharges the sole K029 numeric assumption `replies[4]<P`; `caller_product_domain` derives that at the saved lineX/lineX call. `row_continuation` reuses NEW contextual substitution for subsequent double/sub. |
| Imported prefix product local log | `NEG_PrefixStep.multiply` (existing all-raw law), strengthened/reused `NFB_MulDischarge.multiplication` | Same saved arbitrary product and SAME `flat[index]`; all raw operands. `NET_PrefixClosure.step/observed_result` and existing NET native window pairs retain exact buffer/window and call association. No NEV pending audit promotion is used as new credit. |
| Imported `NET_back_product` two-entry reverse log | `NEW_GeometryArithmetic.multiply_probe` plus `NFB_MulDischarge.multiplication` | Same saved suffix and SAME prefixes[i]/flat[i]; all raw operands. `NEW_GeometryReverse.state/ordered_calls` compose arbitrary one-cell native frame observations on the same evolving inverse list. |

The native observations are caller logic with unconstrained saved replies.
These laws instantiate those replies in Lean; the native harness never assumes
or proves a field product. A pairing does not by itself close the native root.
P6/D188 option-A semantic transport is retained and reported as reclassification.
