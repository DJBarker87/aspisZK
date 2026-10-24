# Exact native Field projection transports

`S9QuadraticFieldMulProjectionV1.quadratic_field_mul` proves that the Field
multiplication projection inherited by a quadratic algebra equals its direct
quadratic multiplication. The base field, quadratic parameters and operands
are opaque. `S9PointNativeMulProjectionV1.native_mul_projected` specializes that
source API to the native WideExact carrier, at wideU/0, before any source row
or input observation is supplied. `S9PointExactOperatorTransportV1` uses that
accepted specialization to transport a triple and a scaled finite sum. Its
index type, finite set, scalar factors and summands all remain opaque.

Before/after: the earlier operator identities were valid but captured a
Field dictionary under a smaller import context. They did not suffice to
compose the actual point consumer. This packet proves the corresponding
interfaces in the actual point import context via a generic quadratic API.
There are no new mathematical premises, source-value hypotheses or output
meaning assumptions. The full point row theorem is a separate consumer.

Validation: each smallest changed file was checked first, then its dependent
specialization, then the triple/sum bridge, under the unchanged M4400 cap.
Exact receipts record status, time, RSS, swap, source revision and axioms.
All accepted checks exited zero, used zero swap and only standard axioms.
No concrete field constants or 64/1024-cell rows were evaluated. The rejected
opaque-native rfl attempt is retained, with its original source and receipt.
The Expr diagnostic is syntax evidence only: its summary distinguishes a
wrapper-head difference and nested instance syntax; it establishes no semantic
inequality or security result. Full raw log is pinned by SHA/size, not bundled.

This packet establishes operator identities. Caller/source functional meaning,
release artifact/runtime correspondence, coherent final closure replay, full
spend-relation transport and the 100-bit security target remain separate.
The security target is not yet established.
