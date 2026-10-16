Focused Lean 4.32 evidence; see SUMMARY.json and the design result note.

archive-pin.json identifies evidence.tar.gz. BUNDLE-MANIFEST.json inside the
archive pins every other member. local-verification.json records independent
local rehashing of all 616 pinned members. The archive contains 617 members,
including source snapshots, exact cache/runtime keys and per-target metrics,
logs and axiom reports. Compiled objects stay on the retained host cache;
object and companion hashes are included in the receipts. Identical external
snapshots repeated by each run are represented once in the archive.

The original UNCOMPILED-labelled source and manifest are historical snapshots;
the final source is sources/ExtractedPublicCheckedBridge432.lean, checked in
runs/public-bridge-432-b. No full inventory replay or Rust extraction was run.
Snapshot tooling failure and post-completion SSH cleanup are not Lean failures.
