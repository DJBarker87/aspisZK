# R439 saved translation source-custody audit

`audit_translation.py` independently checks the collected R439 translation result, launch/collection status, exact input and pinned translator hashes, source revisions, command payload, GNU time metrics, cgroup limits/events, generated-file hashes, manifest binding, warning list, and external template files. The saved run is under `translation-runner/output/54e804310fa3-20261003T050407Z/`; the matching launcher record is in `translation-runner/launch-history/54e804310fa3-20261003T050407Z/`.

The run completed successfully: launcher, collection, translator, and GNU time all returned 0. Translation wall time was 0.61 seconds, peak RSS was 91,520 KiB, and GNU time and cgroup report zero swap. The cgroup used MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, and TasksMax 128; cgroup memory peak was 160,153,600 bytes with no high/max/OOM events. The input was the SHA-pinned 40-group projection. The source Fun284 row is selected with TraitImpl47/FnMut trait9/method0, and output manifest rows uniquely report function 284 and trait implementation 47 implementing trait 9.

The generated bundle retains the entire callback definition, the FnOnce `call_once` bridge and FnOnce/FnMut dictionary definitions, the field and closure types, and the generated pending-return carrier type. The manifest contains 20 functions, 6 types, 2 globals, 2 trait implementations, no trait declarations, and no opaque functions. The generated `Funs.lean` and `Types.lean` contain no `axiom` declaration lines, and no external template files or warning lines were produced. This is a generation inventory, not a Lean compilation or `#print axioms` result.

The checker compares the complete executable body of generated Fun284 with R174's `rawCallMut` body. After normalizing the single field namespace prefix (`aspis_core.field.` to `field.`) and formatting whitespace, every body token is equal. The declaration names differ, and the generated tuple input type has explicit grouping parentheses around the product type; both signature headers and their hashes are preserved in the report. This comparison does not establish that the generated body implements the frozen Rust callback.

Run from the repository root:

```sh
python3 .r21-scratch/r439-closure-execution-preflight/source-custody-audit/audit_translation.py
```

The checker writes only `audit-report.json` in this directory. It performs no build, translation, or remote operation. The report records hashes for all saved run and launch artifacts so their contents remain auditable.
