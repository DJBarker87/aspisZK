# NJG findings and excluded drafts

Target not yet established.

F1 (own statement error, L013): the draft round frame length896 confused payload size with the full framed record. The actual NGX_PrefixGeometry.width is5+payloadSize; rows15..24 have payload896 and full frame901. That896 statement is false and receives no credit. Corrected theorem uses901 and preserves the full frame. No inherited/source claim is changed.

L012 imported an unnecessary historical JFv_SemanticDecode object which required absent PSem_Root. The unused import was removed; no historical owner/object is rewritten.

K001 never reached verification: exact KMX realloc uses allocator_api, so scratch crate needs a cfg(kani)-only feature gate. L008 adds that gate; no assertion changed.

F2 aggregate row write, arbitrary allocator/abort-prefix interpretation, round callee-domain/Code chain, terminal256, finish136 and complete op9 association remain unproved. Native one-word KMX success does not supply them.
