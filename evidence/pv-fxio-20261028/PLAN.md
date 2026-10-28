# FXIO boundary check

Base: 10b8afe7647d478f70693d8fc12e07be871c91e0. Branch:
codex/pv-fxio-20261028. Assigned worktree is unchanged. Host directory:
/home/dombarker/project-offloads/codex-pv-fxio-20261028/.

Budget: at most 100 Lean attempts, zero Kani. Only IDs 35800–35899,
with 35897–35899 reserved for audits. No changes in crates/ or programs/.
Read all common rulings through (m'), (k'), (r') and (h6), restored flag,
r1p-common, local-lean, root AGENTS security discipline, D42–D68, trust contract,
owner-adoption ledger section, recount6 target rows and V184 closure template.
Recount6 and the external manifest are read from pinned research git objects;
they are absent at the candidate base. input-pins.jsonl records their identities.

First resolve the V175 same-input world obstruction before building row
closures. Native finite validation must execute identical create_new arguments
in an absent then present filesystem world. A Lean proof must state exactly
what fails: a single fixed pure callback and fixed result decoder across both
worlds. No inference of native insecurity, crash durability or impossible
world-indexed interpretation follows. If confirmed, stop at the user's checked
counterexample condition; do not spend the compile budget on refuted closures.

Trust T stays entropy_law, entropy_kernel, observation. The first two cover
successful entropy draws and joint density, no filesystem facts. observation
covers native/extracted file outcomes, filesystem state, ordered calls and
complete observer payload equality. It does not independently guarantee open
success, exclusive creation, write progress, post-error rollback, fsync crash
persistence, close-once ownership or witness-independent failure probability.
Those are source/world P obligations; no new T item is installed. A stronger
OS durability/atomicity assumption, if needed, must be reported for owner
consideration, not inferred from observation equality.
