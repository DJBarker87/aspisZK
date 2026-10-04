# R759 transport-leaf compile audit

- 196 generated transport leaves are unique and exactly match the sorted 196
  nonzero leaf positions in the R748 plan: `True`.
- Seven focused chunks are green; their 196 full axiom reports are all
  `[propext, Classical.choice, Quot.sound]`.
- The initial pre-parser-fix emitter source and failure log are retained. The
  changed parser retry generated then `--check`ed the exact seven sources.
- Import source and remote olean checksums are recorded in the JSON and
  `r759-import-olean-sha256.txt`.

This is a finite transport table. It does not prove a full point-weight value,
source chord execution, a matrix property, native correspondence, privacy, or
security.
