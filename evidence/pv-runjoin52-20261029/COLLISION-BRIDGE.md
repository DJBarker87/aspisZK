# Collision separation design (runjoin52, before Lean edits)

Entry ef805d853cdd61a323b0fa3b3b0646d25828e065, same worktree and branch.
Neither authoritative generated Types source is edited, renamed or replaced.

The neutral carrier is four U32 coordinates for a QM31 value and a pair of
those tuples for a circle point; U32 belongs to the common pinned Aeneas
standard library, not either generated Types module. Errors and outer
failure/divergence remain explicit. A neutral kernel module imports Aeneas
only, defines the ordered arithmetic/control computation and proves transport
by symbolic bind lemmas. No generated structures occur in its interface.

An owned-only adapter maps the owned carriers and complete Results to these
neutral tuples. An R72-only adapter maps the EJR-selected carriers to exactly
the same tuples. Each side proves its projection/round-trip and source-call
facts independently. Shared arithmetic and control lemmas must live in
neutral modules with neither generated Types module in their transitive
closure. A neutral combination module imports those neutral modules only.
The generated-type adapters themselves must never be co-imported: Lean imports
are transitive even when a theorem statement mentions only standard types.

A theorem cannot be moved out of a generated-type import closure merely by
restating its conclusion over tuples. Source-specific adapter laws remain
separately checked certificates; the final neutral theorem may consume only
facts actually proved in the neutral closure. It must not assume the desired
source equivalence or represent the two side certificates as discharged by
an unchecked import-free export. Any remaining source-to-neutral arithmetic
binding is recorded as open, without whole-row credit.

Next consumer: the actual stored two-circle association at the original
common sample, before backend hinput, FinishContext or publication. Step (4)
remains prohibited. No change to trust, guards, games or endpoint premises.

## Implementation refinement

The neutral sides are `CircleRawScalar52`/`CircleRawTower52`/
`CircleRawMap52` and `CircleR72Raw52`. They define the computations over
standard tuples without importing either generated Types module. The two
generated-type adapter families prove independently that these computations
encode the actual authoritative source calls. `CircleNeutralBase52` imports
only the neutral sides. It does not import or export source adapters.

R72 has checked arithmetic and guarded r23/r24 multiplication; the owned
side uses wrapping CT operations. Equality is required on the produced
canonical domain, with intermediate canonicality derived rather than
assumed as a source-caller premise. An unrestricted all-raw-input equality
is neither proposed nor credited.

Attempt 65520 reached the heartbeat limit comparing bare inverse functions.
The replacement at 65521 uses function extensionality on the already checked
scalar inverse transport, then the generic inv_with transport. No inversion
chain is unfolded and no limit is raised.
