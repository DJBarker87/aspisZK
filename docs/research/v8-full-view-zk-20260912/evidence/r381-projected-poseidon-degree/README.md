# R381 evidence bundle

This bundle preserves the promoted Lean source, all three focused-run source/log/receipt triples, runner, direct and transitive local import source copies, the pinned polynomial API source copy, and the existing selected-source selector and pow5 provenance excerpts. `inventory.json` records every path/hash, run measurement/resource scope, complete axiom report, and the first remaining source obligation.

Run `python3 verify_evidence.py` here for offline verification. It does not invoke Lean, fetch source, or rebuild a cache. Failed drafts are retained as failed history, not successful proof results. The source excerpts do not establish that the Lean expression corresponds to Rust execution.
