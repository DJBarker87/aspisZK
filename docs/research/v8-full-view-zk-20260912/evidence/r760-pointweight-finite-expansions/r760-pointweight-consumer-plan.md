# R760 point-weight consumer plan (source-only)

Input leaf plan: `.r21-scratch/r748-chosen222-point1-leaf-plan.json` SHA-256 `55f19bf194589ef1229ae6d96ce0d7ef16b1b8d3466b40d00cc0e9fa4b906dd4`.

The selected 222-column point1 row needs **343** `pointWeight` values and **519** distinct transport leaves. Of these leaves, **196** have nonzero point-basis values and are supplied by the seven green scratch R759 chunks; **323** are zero by the existing R754 guarded support chunks. The plan does not recompute any field values.

For a value at `n`, the planned proof unfolds `sourceChordTranspose` at that one parity branch. It rewrites named finite `sourceGather` / nested-gather schedules first, then rewrites only their listed leaves with R759 or R754. It must not unfold a 1024-entry mask, decide an `univ` membership, or use a broad field reduction.

The generated gather artifacts have a green densest prototype `.r21-scratch/r748-gather-schedule-generator/PrototypeDensest255.lean` SHA-256 `1e8086e99dc42e379589a2db7df47bf25859cba0117baa8974e44bdd536ad1fa`. Per lead status, all generated Loop and Expand chunks are green; Nested00 is green and Nested01–04 are compiling. They remain scratch artifacts until their evidence/promotion is complete; a consumer may use only focused-green schedule modules.

A future consumer is proposed as 11 chunks of at most 32 point-weight values. The full exact value-to-leaf inventory, source hashes, and proposed chunk lists are in [r760-pointweight-consumer-plan.json](r760-pointweight-consumer-plan.json). It requires lead review and focused compilation of each needed schedule module before any consumer compilation.

This is an indexing and dependency plan only. It proves no source execution, rank, H1 compatibility, oracle law, privacy, or security.
