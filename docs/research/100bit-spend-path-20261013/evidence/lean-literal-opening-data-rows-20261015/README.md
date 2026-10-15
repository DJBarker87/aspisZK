# Literal opening data rows focused evidence

This bundle preserves three local focused attempts for `R1LiteralOpeningDataRows`: two failed proof attempts and the final successful compile. The theorem proves a deterministic identity for `RawOpening.withRows` given explicit equality hypotheses for the selected functionals and raw base functional. It does not establish transcript acceptance, causal recovery, or a source/runtime correspondence.

The final attempt reused the existing local focused Lean cache. It completed in 123.136 seconds, with 3,933,024 KiB sampled aggregate process-group RSS, 3,951,607,808 bytes maximum RSS in the time log, and zero swaps. The command used Lean memory limit 5000 MB, a 7 GiB sampled-process stop threshold, and a 900 second timeout. There was no cgroup. This is not a cold transitive replay.

The two direct imports and their cached objects are pinned in `source-manifest.json`. The bundle keeps their source snapshots and exact object hashes, plus the final source/object, runner and all attempt logs. `R1RawOpening` source is copied from the retained reuse checkpoint; `R1SelectedOpeningFunctionals` source is copied from its focused evidence bundle. The import object files came from the local focused cache overlay. The provenance is limited to the recorded attempt receipt and direct imports; no broader cache lineage is asserted here.

All attempt source snapshots, stdout logs, time logs, JSON receipts, direct import source pins, final object, and runner files are included and checksummed.
