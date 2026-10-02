# R210 diagnostic projection

This projection keeps exactly function bodies 9, 49, 50, 91, and 92 from R207. Every other function body is marked `Opaque` and every other function opacity is set to `Foreign`; signatures, types, trait declarations, and trait implementations remain unchanged.

The projection first decodes the complete global hash-cons table, then re-emits first surviving occurrences as `HashConsedValue` and subsequent references as `Deduplicated`, preserving IDs and decoded values. `R210-projection-audit.json` records input/output hashes, removed body IDs, and per-retained-function decoded SHA equality. This is diagnostic only: opacity is not accepted as a proof premise. No Aeneas translation or compilation was run.
