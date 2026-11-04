# Native geometry oracle and field-law table

No new multiplication body runs in Kani. The inherited source-shaped
`NEW_geometry::NET_back_product` records its operands/reply in a LOCAL mutable
record; the reply is arbitrary. It is an opaque caller observation, not a
Kani proof of a field product and not a credited callee arithmetic stub.

| Observation | Lean substitution theorem | Domain |
|---|---|---|
| `NET_back_product(suffix,prefixes[i],reply0,log)` | `S7Kani2PrefixLoop.multiply_word` and inherited `NEG_PrefixStep.multiply` | All raw U32 operands; actual model result is `ok (wordMul suffix prefix)` |
| `NET_back_product(suffix,flat[i],reply1,log)` | same named theorems | All raw U32 operands; identical saved suffix, same flat/prefix buffers and index |

`NEW_GeometryReverse.Trace` is deliberately defined AFTER this substitution.
It does not manufacture native trace existence. `state` associates the SAME
mutable buffer and returned suffix with the inherited inverse driver;
`ordered_calls` retains both operands of every call in reverse-cell order.
No arbitrary reply is accepted as a natural-product theorem. Root closure
still requires the actual physical trace and all other pending geometry gates.
The exact inherited multiplication theorem statements/axioms will be audited
in the final co-import; only standard axioms are admissible.

KMX copy stubs are exactly the approved patch. Positive/negative fidelity
controls must match each credited source configuration. No custom copy stub,
writable static, function-pointer result or function-contract credit is used.
