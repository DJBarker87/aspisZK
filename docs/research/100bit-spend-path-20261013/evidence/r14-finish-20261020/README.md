# R14 finish proof packet

See `../../design/R14-FINISH-20261020.md` for theorem coverage, definition
locations, exact remaining premises and verification scope.

- `accepted-summary.json`: twelve current-source exit-zero targets, 26 theorem audits.
- `manifest.json`: all compile attempts, including rejected and superseded attempts.
- `<attempt>/`: command, source/import hashes, output, time/RSS/swap and receipt.
- `adapter-binding.json`, `generate_adapter.py --check`: exact emitted finish bodies,
  with only typed backend substitutions and namespace changes.
- `source-pins.json`: all 58 frozen inputs match; includes the freeze's LLBC comparison.
- `verify.py`: checks current accepted source/dependency hashes and standard axioms
  without compiling Lean; regenerates metadata summaries.
- `check.py MODULE ATTEMPT`: focused compile under the shared mkdir lock and
  -M4400 limit, into this branch's private object directory.

This is inherited-cache focused evidence, not a fresh coherent release replay.
No binaries or compiled Lean objects are committed. Historical failed recovery
logs may print sorryAx; accepted receipts and the final audit do not.
