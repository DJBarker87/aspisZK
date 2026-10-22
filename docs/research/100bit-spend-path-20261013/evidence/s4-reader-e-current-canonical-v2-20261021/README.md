# S4 current Reader.e canonicality v2

This leaf proves that a successful current Reader.e operation cut returns a WideExact whose eight coordinates are each below 2147483647. It uses the exact generated Reader.e body with only three declared callee substitutions and the dependent raw-reader ABI; the body checker preserves the remaining operation order and control flow.

Version 2 removes the old Stage2AdoptedReader carrier from the FS module. Its concrete decoder adapter maps the retained RecordParser WideExact result field-by-field to the current Stage2 carrier, then applies the existing ExtractedRecordByteCanonicality.slice_success theorem directly. The direct imported sources, selected object hashes, exact OLean closure overlay manifest, launch, time, and axiom logs are retained. The prepared overlay is broader than this module's loaded imports; it is documented for reproducibility but does not cause the removed Reader module to be imported.

Both exported theorem axiom reports are [propext, Classical.choice, Quot.sound]. The result remains conditional on successful Reader.e and does not establish outer resume reachability or Aeneas soundness. No OLean binary is included.
