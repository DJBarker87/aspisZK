# NEW local opaque field-call observations

See NEW_STUBS.md. No arithmetic kani::stub is credited by this lane, and no
field multiplication is proved in Kani. Reverse probes retain local records
of both inputs and the arbitrary returned word; only the named Lean law may
substitute the actual multiplication value. Callers must establish the same
operands, buffers, index and saved suffix. No writable static is used.

| Opaque observation | Paired emitted/model law | Domain |
|---|---|---|
| NET_back_product(suffix,prefixes[i],reply0,local_log) | S7Kani2PrefixLoop.multiply_word; NEG_PrefixStep.multiply; NEW_GeometryArithmetic.multiply_probe | All raw U32 operands, actual emitted multiplication returns the probe word product; no canonical-only precondition is imposed |
| NET_back_product(suffix,flat[i],reply1,local_log) | Same laws | Same all-raw domain; same saved suffix and ordered second call |

NEW_GeometryReverse.state/ordered_calls compose the substituted trace with
model reverse induction; native trace existence and final physical root join
are not manufactured. NEW_L079 separately associates actual emitted field
children with the adopted model. The only copy stubs are the exact approved
KMX patch, with matched failing controls; they are not field arithmetic stubs.
