# Strict import-wide axiom audit

## Scope and method

This packet audits the separately pinned L188 roots
`AspisR1.RPx_Deployed.deployed` and `AspisR1.JHx_Joint.source`. It addresses
missing obligation 3 in `evidence/native-l188-20261028/NDJ_RELEASE_MANIFEST.md`.
It does not establish the overall release security target.

`NDP_Audit.lean` enumerates every `ConstantInfo.axiomInfo` in the kernel
constant map with exporting disabled, resolves each declaration's defining
module through `getModuleIdxFor?`, and records its universe parameters, full
pretty-printed type and exact kernel expression. It independently scans all
loaded modules' serialized constant tables and requires equality of the two
axiom-name sets. No axiom is filtered by namespace, generated status, intended
use or apparent harmlessness.

The root's actual module closure is computed from the imported module-header
DAG. Extra imports needed only by the metaprogram are explicitly marked and
excluded from the root inventory. Every imported module, including modules
containing no axioms, is recorded in the Lean stdout logs.

The raw dependency walk starts at the named root and exhausts a worklist of
constants occurring in declaration types and values. `value? true` includes
opaque proof bodies. Inductive constructors are added, matching Lean's axiom
collector; constructor/recursor types are inspected as ordinary constants.
Already visited constants prevent cycles. A missing reachable declaration or
module is fatal. This is syntactic constant-dependency reachability, without
unfolding or reducing concrete arithmetic terms. It does not substitute
module-import reachability for proof dependency reachability.

The resulting axiom set must equal Lean's `collectAxioms` output (which may use
imported summaries). Each root also has its own `#print axioms` line. Compressed
sorted visited-name files provide independently checkable membership and
nonmembership evidence. `NDP_validate.py` decompresses and hashes these files,
checks every emitted axiom's membership, recomputes the import closures, checks
the printed sets, and joins both forests without silently merging differing
axiom declarations.

## Provenance and interpretation

The task cache is
`/home/dombarker/project-offloads/codex-cx-axaudit-cache-20261028`.
Its `objects/` and `joint_objects/` were copied from the read-only L188 cache;
no source object was changed, linked in place, or deleted. The own cache is
retained. `NDP_verify_seed.py` verifies every copied artifact, including private,
server and IR companions, against the predecessor's manifest SHA256 and size.
The original manifest and source/object provenance remain in the L188 packet.

This is an audit of declarations in pinned compiled objects, not a fresh
recompilation of their source dependency closure. Source template text that is
not in the actual imported compiled module is not a logical declaration in
this environment. All actual imported `FunsExternal` modules are scanned by
both enumeration paths; their per-module axiom counts are also listed in the
final JSON. No external-template exception or namespace whitelist is used.

The two roots retain separate coherent predecessor forests. Their historical
combined-import duplicate-declaration failure is retained in
`evidence/native-l188-20261028/NDJ_IMPORT_FINDING.md`; this task does not repair
or claim a compatible shared environment.
