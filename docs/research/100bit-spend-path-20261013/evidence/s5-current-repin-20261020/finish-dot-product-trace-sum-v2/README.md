# S5 ordered finish field-product trace packet v2

This theorem strengthens the field-product result with a single ordered list that records each actual field read and weight read. It proves row count, ascending query indices, successful read correspondence, and that the same trace's product sum decodes to the returned `finish_query_dot` output.

Its direct FieldProduct dependency was freshly rebuilt against the exact Delta source/object chain included under `upstream/field-product-v2`; that bundle includes the Delta source and NUC receipt plus the exact accepted DecodedValue predecessor source/object receipt. The trace itself was freshly compiled against the rebuilt FieldProduct object. All audits are standard-only. No compiled objects are included. This is a focused successful-call theorem, not the complete outer Claim/runtime proof.
