# R13 refinement packet

Status: partial, R13 OPEN. See `../../design/R13-REFINE-20261020.md` for
checked source citations, theorem scope, explicit premises and the exact
remaining proof obligations. `audit.json` records seven successful final
modules and sixteen standard-axiom theorem audits. `manifest.json` includes
all eleven compile attempts, including four historical elaboration failures.
Only the final successful source hashes are release evidence.

Reproduce the metadata audit (no Lean replay):

```
python3 docs/research/100bit-spend-path-20261013/evidence/r13-refine-20261020/extract-terminal.py
python3 docs/research/100bit-spend-path-20261013/evidence/r13-refine-20261020/audit.py
```

`compile.py ModuleName` is the capped, locked focused compiler harness.
Do not rerun unchanged successful modules just to refresh receipts.

Proved: concrete carrier/grammar transport; exact source leaf slices/tags/salts
under named WIRE boundaries; exhausted source terminal conditions; exact model
read-set/path-family equality; model dedup/padding to executable per-query
path/leaf programs; conditional source-leaf/model-opening composition.

Unproved: source sort/key/dedup and mutable-array level simulation; source slot
padding scan; whole source-run accepted-read equality and caller composition.
The stage-1 binary batch-A caller remains an S7/stage-1 re-pin dependency.
There is no unconditional accepted-source-run implies Bin acceptance theorem
in this packet. No verifier or existing Lean module was changed.
