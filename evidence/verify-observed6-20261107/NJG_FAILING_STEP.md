# NJG findings and excluded drafts

Target not yet established.

F1 (own statement error, L013): the draft round frame length896 confused payload size with the full framed record. The actual NGX_PrefixGeometry.width is5+payloadSize; rows15..24 have payload896 and full frame901. That896 statement is false and receives no credit. Corrected theorem uses901 and preserves the full frame. No inherited/source claim is changed.

L012 imported an unnecessary historical JFv_SemanticDecode object which required absent PSem_Root. The unused import was removed; no historical owner/object is rewritten.

K001 never reached verification: exact KMX realloc uses allocator_api, so scratch crate needs a cfg(kani)-only feature gate. L008 adds that gate; no assertion changed.

F2 aggregate row write, arbitrary allocator/abort-prefix interpretation, round callee-domain/Code chain, terminal256, finish136 and complete op9 association remain unproved. Native one-word KMX success does not supply them.

F2 (own rule-D precondition finding): K012/K013 initialized a word in the CURRENT destination row before the call, then read it on the decoder Err arm. The actual claims loop leaves that row uninitialized. Its no-write conclusion on that artificial prestate is mathematical support only and cannot be caller credit. The correction removes every current-row pre-initialization and every Err-arm current-row read; only a word in an already initialized prior row(q<p) is observed when p>0. Returning rows are read only after actual store success. K015/K011 args and K012/K013 result must be re-established with the original harness names and stronger/generalized valid prestate before use. No earlier row was admitted, so no CLOSED status is lost.

F3 (source-model callback domain): fresh release MIR wraps16+i in the salts closure, while the adopted cohort checks the addition. An unrestricted arbitrary from_fn dictionary could call outside the array builder's range and distinguish those bodies. NJG_FromFnCongruence and NJG_FinishClosures prove the replacement on actual visited i<10; NJG_FinishInstall installs the existing ordered std builder rather than assuming an unrestricted callback law. Both original/replacement forms and extraction pins are retained. No frozen source or security metric is changed.
