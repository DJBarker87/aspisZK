# Symbolic source Result composition

The combined square/mixed-product cut QM31.mul maps to the genuine QM multiplication cut with the same nine source calls, output words and full Result behavior. The generator distinguishes every source and target binder and emits applications of the accepted component/transport lemmas; kernel checking verifies the complete source graph against the generated statement. `generate.py --check --output qm-product/sources/S9GeneratedCombinedQMResultV1.lean` reproduces the accepted source without writing it.

A separate generic bind lemma permits continuation correctness to be required only on reached successful source states. It preserves errors/divergence; a concrete consumer must still derive its reachable-state invariants. This packet does not establish the outer mixed operation or square, the complete caller, or release runtime correspondence. Focused checks, source pins and standard-axiom reports are retained; compiled objects are excluded.
