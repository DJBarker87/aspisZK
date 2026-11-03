# NER final loaded scan

**Complete: zero dangling references.** NER_SCAN.json records the final result;
NER_LOADED_final.jsonl.xz contains one row per module, with canonical and raw
loader imports, declaration counts, edge counts and missing-reference details.

The checker in NER_FinalDriverV2.lean loads the two roots privately with
importAll. For every module-owned name it obtains the checked kernel declaration
and follows types, theorem/opaque values, constructors, recursor rule bodies,
and constant-name metadata. Missing own declarations or referenced names fail.
Imports use exactly the stable first-occurrence projection of the original
NER_ModuleTables index; extra, removed or reordered imports fail. Raw loader
lists remain available for independent reconstruction.

A901 passes for 16,058 modules, 1,520,745 active declarations and 38,049,122
reference occurrences. All recorded canonical import lists match. Both raw
root walks also complete and equal collectAxioms with the standard three axioms.

A900's gate failure is preserved in NER_A900_DIAGNOSIS.json and
NER_LOADED_A900.jsonl. Its zero missing references were accompanied by 13,935
raw-list mismatches caused solely by duplicate loader imports. Applying the
index's existing stable projection matches every module, including order.
The original serialized entry count includes public/private duplicates; its
unique-name count equals the loaded declaration count for every module.

Original dangling/body-removal/import-drift controls and negative validator
mutations remain in NER_tests.py. R031 additionally exercises the exact V2
checker on a planted recursor reference and matched control, and rejects three
import mutations. R032 checks the final driver. NER_final_checks.py validates
the final scan, cohort, receipts, source hashes, reachable archives and results.
The historical incoherent scan is preserved as NER_SCAN_PRE_REBUILD.json.
