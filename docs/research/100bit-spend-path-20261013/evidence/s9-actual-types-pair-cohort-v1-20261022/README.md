# Actual field reader → Pair reader source cohort

This source-only cohort contains a collision-safe Actual field carrier, its fieldwise map to the retained Owned carrier, mapped `from_limbs` / `from_le_bytes` / selected field-reader bodies, the reader canonicality derivation, a joint Actual+Pair type import check, and an Actual-reader → Pair-reader bridge.

The final theorem is `AspisR1S9ActualPairFieldReaderBridgeV1.actual_weights_field_maps_to_pair`: it maps the complete `Result` of the selected Actual field reader to the Pair reader call. `actual_field_success_pair_canonical` derives Pair-side canonicality from the same successful Actual call through that full-result map and the retained Pair reader provenance theorem. It does not establish upstream caller index bounds or successful argument reads that are not premises of those source calls, and it does not establish a frozen binary/source correspondence.

`COHORT-MANIFEST.json` records source/object hashes, direct import owners, compiler and runner pins, exact receipts, resource measurements, printed axiom reports, and retained failed-attempt references. Object files fetched for root follow-on are staged separately under `/tmp/s9-actual-pair-cohort-v1-20261022/objects`; they are not part of this packet. Runner and collector scripts are in `tooling/` with hashes captured in the manifest.

Attempt39 and attempt40 logs for the failed joint-import and first bridge drafts are retained under `failed-attempts/`; neither failed output is treated as accepted. The accepted collision-safe source normalization is documented in the parent candidate's `SOURCE-NORMALIZATION.md`: Actual attempt7 Types declarations were preserved while the discriminant attribute was replaced with an explicitly named, uniquely qualified instance to prevent collision in joint imports.

Check the source/evidence packet and fetched objects with:

```sh
python3 docs/research/100bit-spend-path-20261013/evidence/s9-actual-types-pair-cohort-v1-20261022/check_cohort.py --objects /tmp/s9-actual-pair-cohort-v1-20261022/objects
```
