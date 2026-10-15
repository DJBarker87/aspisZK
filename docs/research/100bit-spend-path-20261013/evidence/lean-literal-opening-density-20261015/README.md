# Literal opening-row density bounds

`R1LiteralOpeningDensity` compiles the four row-specific independent-answer bounds for literal rows 27–30 (gamma, kappa, first fold, second fold). Its readers are causal: the context comes from the completed prefix and current literal message, while each bound is for the row’s fresh challenge. The constants are `336869026622539 * gammaAtom`, `600 * atom`, and `9396508281846 * atom` for each fold row. The theorem uses the existing selected opening mass bounds; it does not prove D3/shared-oracle closure, terminal acceptance, or Rust source correspondence.

The `none` branch of each reader is defined as the empty event and contributes zero to the local mean. A terminal acceptance argument must separately establish that the required readers succeed on admitted executions; otherwise those executions would be absent from these local event bounds.

The single attempt `literal-opening-density-a` succeeded in 1.69 s with 3,594,936 KiB peak RSS and zero swap. It emitted eight standard axiom reports. Direct import sources and objects, pinned runner files, receipt, logs, time record, and the final object are retained and hashed in `source-manifest.json`.

Object-storage note: the canonical compiled objects are the byte-identical members of `literal-opening-density-objects.tar.gz` listed in the manifest. Loose duplicate `.olean` files were moved outside the bundle to `/tmp/aspis-r1-retained-loose-objects-20261015/lean-literal-opening-density-20261015/`; archive members and object SHA-256 pins were not changed.
