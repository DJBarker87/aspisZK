# Two-transaction frozen decision packet

Run focused checks in dependency order with:

```
python3 -B tools/dv-twotx/compile.py MODULE
```

The runner uses the prescribed Lean 4.32 executable, `-j1 -M4400
-DElab.async=false`, the shared mkdir lock and a private object directory.
It reuses historical pinned object paths from the existing port packets and
refuses an unchanged source/dependency retry. It never overwrites a shared
object. Each attempt records exact commands, source/revision and direct-import
hashes, exit, wall time, peak RSS, swaps, errors and full axiom output.

The final focused union is `OraclePortFrozen2Freeze`; it is run once after
all individual new modules compile. It is an import/axioms audit on the
cached dependency base, not a complete frozen release rebuild.

```
python3 -B tools/dv-twotx/audit.py
```

The latter validates final source snapshots, receipts, current direct imports,
standard axiom sets, theorem audit coverage, scope and the 5 MB JSON limit,
then writes `audit-summary.json`. It launches no Lean process or solver.

See `docs/research/100bit-spend-path-20261013/design/DV-TWOTX-20261021.md`.
