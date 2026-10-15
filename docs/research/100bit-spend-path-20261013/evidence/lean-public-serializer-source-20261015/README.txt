Exact extracted serializer: coordinator focused checks, 2026-10-15

The generated Types/Funs are byte-identical to frontier-c-enums extraction
from source integrated at781929374. The initial Lean4.32 import failed because
the cached Aeneas backend is Lean4.31. No cold dependency build was attempted.
The retained Lean4.31 cache was then used read-only: Types/Funs/Audit exit0;
wall24.436/18.197/24.654s, sampled group RSS2538176/2810976/2510272KiB.
Eight audit declarations report only propext, Classical.choice and Quot.sound.
All process swap counts are zero; this does not assert zero system swap.

The actual Rust serializer differential tests pass2; the saved R1 proof core
call-count regression passes1 after the serializer source change. Native wall
87.683/56.947s and sampled group RSS730416/643072KiB. Commands and source hashes
are in their receipts. No proof generation or SBF/host job was run.

The 7GiB process-group monitor and Lean-M6000 are local guards, not cgroups.
Each target was checked individually, then axioms once; no full replay.
Runner source_base_revision is a retained older integration-base label; use
checkout_head, source_sha256 and pins.json for the exact checked declarations.
The cached backend's existing compiled objects are trusted imports, not a new
backend replay. Binary/source reproducibility was not independently proved.

Compilation is not SourceSerializerRefines. Whole-serializer refinement,
source semantics/extraction trust, caller amount validation, omitted metadata
binding, and Lean4.32 integration are OPEN. No J1.a closure is claimed.
