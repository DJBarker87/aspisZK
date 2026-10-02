# R368 evidence bundle

This bundle preserves the successful R368 wire compatibility Lean source and the two rejected drafts that preceded it. `inventory.json` records source, dependency, runner, exact run metrics, resource limits, and all complete axiom reports. `verify_evidence.py` is read-only and uses only paths inside this bundle plus the promoted target and direct dependency beside this evidence directory.

The source provenance is the saved R368 selected semantic terminal census under `source-provenance/`. Its frozen `performance_verifier.rs` excerpt records the selected `semantic_cached` branch: it places the sent constant at coefficient 0, copies the transmitted high coefficients beginning at coefficient 2 (therefore omitting coefficient 1), computes that coefficient from the current claim and other sent values, then compares the terminal result with the retained claim and returns `Error::Terminal` on mismatch. The census is source inventory, not an execution proof. The separate R365 hard-privacy census is unrelated to this selected semantic source path.

The Lean result proves a generic polynomial reconstruction and a generic `Except` terminal guard. It does not establish Rust execution correspondence, an actual terminal degree proof, or universal C1/H1/G. No callback chronology, privacy, or security conclusion is included.
