# R458 indexed tape and scan component

R456–R458 compile successfully from the recorded sources. The indexed tape permutation acts on accepted coordinates, leaves rejection markers in place, and preserves length/status. R457 proves the first-accepted result and drop/tail offset behavior. R458 proves scan count is bounded by list length, count equals length when the result is `None`, and a `Some` result implies positive count. It does not assert the converse for `Some`.

The result is about the abstract indexed tape/list model. It does not prove the actual source sampler’s tape law or full four-limb joint uniformity. The accepted R458 compile targets the canonical `AspisV8R19.R458ScanConsumptionBound` module. An earlier file-path compile is retained as superseded module-identity history. See [the component evidence](evidence/r458-indexed-tape-scan-component/README.md) for source hashes and complete run records.
