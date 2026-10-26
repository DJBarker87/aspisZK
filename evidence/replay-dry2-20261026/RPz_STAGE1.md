# Source and trusted-base preflight

Corrected RPz budget at relaunch: 0/600 Lean attempts, 0 Kani. Previous RPy's
361 Init attempts belong to the explicitly superseded scope, retained as history.
Research source input bb0b0f5b12; source plan stamped a51c005d86 (evidence-only
commit). Prefer exact historical source hashes, then canonical repository paths;
source-selection change from the initial plan is retained in git. 4,141 selected
repository modules; 108 unresolved source selections. No unresolved source or
failed module is silently replaced with an old repository object. Actual source
imports define replay order; unresolved children block their dependents.

RPz_trusted-base.json pins Lean v4.32.0 commit
8c9756b28d64dab099da31a4c09229a9e6a2ef35, binary hash, toolchain object/sidecar
hashes, selected pinned library cache objects/sidecars and Mathlib lake manifest.
Mathlib revision 81a5d257c8e410db227a6665ed08f64fea08e997. Aeneas cache origin
is the coherent SInt2 object selection; its exact object hashes are pinned.
An upstream Aeneas git revision is not yet independently identified.
All these artifacts are trusted rather than source-replayed by owner scope
correction. RPz_objects contains fresh repository objects only; LEAN_PATH lists
the toolchain before those objects and the isolated RPz_trusted library links.
The original RPy Init objects are preserved but absent from this search path.

RPz_001 exposed missing AeneasMeta transitive library objects in the isolated
trusted links. The initial trusted-base manifest is preserved. Pinned AeneasMeta
objects were added to the trusted base for subsequent modules; RPz_001 is kept
as a failed attempt and will not be rerun. Independent modules continue.
The existing S2W runner and reservation script are unchanged. Preparation and
orchestration scripts only select inputs, invoke these launchers and collect
receipts. Reserve one of the 600 attempts for an explicit fresh-object axiom
query if enough modules are reachable. No new theorem or premise removal.
