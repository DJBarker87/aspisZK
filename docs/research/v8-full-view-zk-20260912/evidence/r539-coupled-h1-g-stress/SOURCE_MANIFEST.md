# Source inputs for the coupled diagnostic

The R117 selected-source snapshot manifest is `R117_UNCHANGED_SOURCE_INPUTS.sha256` and retains the checksums of unchanged source files from the NUC R117 workspace. The run candidate replaces only the performance research driver and its diagnostic helper; these exact files are preserved by SHA under `sources/<sha>/`:

- `performance-current-adapted.rs`: `0b69aa4ebb330a291cee674c4e4244eb214ea2b0add3c1353b41c36f398b7f22`.
- `r17_c1_witness_audit.rs`: `639ca0c362bc41994b7ecdb8825e5914e5330e1e66b0a012d2a6998f6ff5b530`.
- `r17_h1_semantic_audit.rs`: `f16df7cda242734d0de3b64bdec1a1972123d763183211c2aedf22fa054141b6`.
- `payment_extraction.rs`, which includes the semantic-map file: `957060c7556d2a0365c1cb3d2bf0576a72399c6c20bfbb47ea531f110dba54f5`.

The exact selected relation, field, circle and basis checksums appear in the unchanged manifest. The selected relation source matches its existing R508 pin. The diagnostic binaries modify neither the verifier nor library source.
