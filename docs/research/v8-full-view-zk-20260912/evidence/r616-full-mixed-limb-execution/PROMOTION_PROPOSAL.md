# Proposed canonical file mapping (not applied)

If the lead accepts the proof boundary and exact hashes, the corresponding canonical source destinations would be:

- `AspisV8R19/R674TermPartition.lean` from `compiled-sources/R674/R674TermPartition.lean`
- `AspisV8R19/R677C1ChunkCanonical.lean` from `compiled-sources/R677/R677C1ChunkCanonical.lean`
- `AspisV8R19/R616MixedLimbExecution.lean` from `compiled-sources/R616/R616MixedLimbExecution.lean`

The current task only prepares this proposal and its evidence. It has not copied any of these sources into the canonical Lean tree, modified package manifests, staged files, or committed anything. The successful R616 source still contains an old “UNVERIFIED proof draft” comment near its header; that comment is in the exact compiled bytes and is preserved. Any editorial correction would create a new source hash and require a changed-source focused compile.
