# Semantic prefix evidence capture

Captured worktree HEAD and stated source base: `5731808b200ee9784b2ed018b9cb9cd7e51be5a2`. The bundle contains 22 focused target attempts, including preserved failures and intermediate `R1SemanticPrefix-b`, and 14 selected final green target objects. Exact sources, receipts, logs, time logs, and SHA sidecars are retained under `sources/` and `attempts/`.

The final object set is in `target-objects.tar.gz`; it contains only the 14 final target objects listed in `manifest.json`. `SHA256SUMS` covers the tracked evidence files and the archive, excluding loose `.olean` convenience copies under `attempts/` and excluding itself. The JSON manifest records every attempt’s source hash, exit status, time, RSS, swap, resource cap, source `#print axioms` count, observed axiom output, and final-object selection. Green target axioms were checked against `{propext, Classical.choice, Quot.sound}` with no `sorryAx`; failed attempt logs are preserved as-is.

These are focused compile and axiom-log records. They do not establish FS-law, source correspondence, privacy, or release-security closure.
