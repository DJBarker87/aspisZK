# S9 owned field result canonicality

`selected_field_success_canonical` composes the exact owned `weights.field` reader result with the selected-slice byte/limb readback, then proves canonicality in `CanonicalFinish (recordWideToFinish (wideToParser out))`. The packed-limb lemma is the accepted S3 proof shape made available in this module because the old helper was private. This theorem introduces no separate `weights.field` success premise: it consumes the actual selected reader theorem.

The source-cut identity and imported reader chain are linked to [the decoder source-cut](../s9-candidate-field-decoder-sourcecut-v1-20261022/README.md) and [the owned reader packet](../s9-owned-field-reader-readback-v1-20261022/README.md). The reader packet in turn pins the from-bytes and from-limbs maps. This remains a Lean source-translation chain; it does not establish checked-index arithmetic correspondence or runtime/release binary behavior.

No compiled objects are included. The receipt records the exact central compile command, source revision, resource measurements, and standard axiom report.
