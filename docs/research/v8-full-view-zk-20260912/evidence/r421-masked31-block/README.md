# R421 saved evidence

This bundle preserves the single green source/log/receipt triple, runner, promoted source, exact R406 dependency source, and a supplemental copy of the source modules imported by the R406 file or its immediate project-source dependencies. The source/import inventory is intentionally bounded and does not claim a complete transitive source closure.

The compile receipt records R406 as the direct local dependency. The separate supplemental audit records source-file hashes and post-run cached `.olean` hashes; it states plainly that those cache identities were observed after the run, not measured during it. GNU time's Lean-child RSS and the wrapper memory peak are separate measurements.
