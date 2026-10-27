# Decoder and public-loop construction

Accepted L049 IndexPorts checked/wrapping equality on the bounded arithmetic
value domain; L050 Decoder preserves complete Results for limbs, bytes, unwrap
and selected field, and the concrete claim owner port. The field port requires
lane.val < 29, as the actual prepared_claim iterator establishes. An unrestricted
index port was rejected (L047); wrapping versus checked arithmetic differs
outside this caller domain. This is not a shipped-source finding.

L053 PointConstruct.loop/from_zero constructs linked native Dot observations
by induction on remaining iterations from scalar/weight read ports. It does not
assume a whole-loop Result, public sum or output trace. The ports still need
concrete semantic/decoder-domain discharge; no whole-leaf closure is claimed.
L051 rejected parsing without spaces around < iter; L052 needed the explicit
iterator successor equality. Rejected recovery sorryAx prints are excluded.
35 unchanged imports were rebuilt privately L012–L046; no shared cache changed.
All accepted new theorem axioms are standard. Per-attempt targets, revisions,
commands, wall/RSS/swap, source snapshots, admission and library pins are retained.
Through L053: 52 actual Lean compiles, zero Kani; L001 never reached Lean.
