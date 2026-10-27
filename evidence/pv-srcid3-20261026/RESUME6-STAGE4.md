# Scalar and nonlinear source progress; provenance recovery

PortReduce.{source,modulo}, PortMultiply.{multiply,power}, PortAddition.
{source,canonical}, PortField.{multiply,power,addition}, PortSboxStep.
{canonical_set,initial_step,final_step}, PortSboxLoop.{initial_loop,final_loop}
and PortTables.{initial,internal,final_constants} passed focused compiles with
standard axiom reports. These establish actual extracted scalar semantics,
canonical outputs, both complete nonlinear loops, and literal frozen-table
association. They do not establish the external/internal linear-layer,
permutation/parent, or 21 frozen hash-cell equations. PublicCorr remains reduced.

The cache import-header inspection 37211 enumerated 6,493 actual imported
modules, 26,880 edges, all with loaded data. This closes the source scanner's
missing nested-import graph uncertainty; it does not prove source/object
provenance for every package object.

## Rejected formatter profile and restoration

The first Fmt candidate was the repaired HEAD snapshot daeafff8…. I then
selected the older EJR library pin 26ac770d… based on its archive provenance.
That was a meaningful profile-selection mistake: it contains the type axiom
core.fmt.Formatter. Fmt 37136 compiled but is explicitly rejected; the sampler
37146 exited Lean successfully but its standard-axiom validation failed on
that axiom. Both new outputs and own copies were quarantined, and their exact
pre-existing shared objects were restored (hash-checked). No rejected object
is certified as current HEAD evidence. See resume6-rejected-profiles.json and
resume6-quarantine-restoration.json. No forbidden construct was added to a new
proof module and no nonstandard theorem is accepted.

The existing research formatter repair daeafff8… defines Formatter as Unit.
It was rebuilt at 37205; FormatterAudit 37209 checks both the carrier equality
and its empty axiom set. The receipt client now quarantines any kernel-success
output that fails the axiom/report gate and restores its previous shared
object. This changes only the own proof client; no launcher or environment
was edited. The earlier kernel/validation exits are preserved, not rewritten.

## Missing provenance and changed-input replays

The 79 non-projection provenance targets were considered once. The launcher
refused unchanged direct-input triples (exit 67), and none was bypassed in
that recovery pass. Core/package source objects were rebuilt with receipts.
Objects that changed bytes make their dependent closures new inputs. The next
cohort uses complete binary transitive object fingerprints and records the
specific before/after input hashes that justify each replay. This detects real
changes behind byte-identical import-only modules; it is not a nonce or an
unchanged failed-source retry. The unrepaired projection cone remains excluded
until a focused review; one attempt is retained for that review at count 96.
The final three charged attempts remain reserved for the three disjoint full
audit shards.

RunJoin late read-only pin 38dd26a1… publishes EndpointSelection.data, but it
still takes selected/publicRecord families and the fixed-endpoint binding.
SelectedSourceReduction retains dictionary/selection equalities, compile_call
and admission. This is a conditional constructor, not a concrete installed
selection. Admission/row_call retain the original published interfaces.
Deployed PV_Src_Premises is still 5 → 5; target not yet established.
