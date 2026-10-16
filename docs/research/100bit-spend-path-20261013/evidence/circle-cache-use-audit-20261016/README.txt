Rejected Circle object use: read-only provenance audit

Rejected .olean:39ea3fa6eb53446ecf6cd4a3856219165b247c4175cf79a28313a55958b15597.
The prior audit read its actual import header (Init,Init,Mathlib), which differs
from the pinned current CircleGroupOrder source's focused imports. The source
correspondence was rejected; unchanged current source and the sampler's three
dependents were recompiled separately in qm31-source-rank-current-backend-20261016.

The R17 primary public/parser/current-QM69 receipt graph and its complete
5502-module external snapshot exclude Circle and the rejected hash. All69
receipts' direct object hashes equal their recorded upstream receipts/snapshot.
In particular, the final41-project-module public bridge is unaffected. The
separate local live PublicCodecAgreement21-project-module cache also excludes
Circle. This is a targeted provenance result, not a fresh replay or blanket
endorsement of every other historical cache mapping.

The separate semantic-prefix bridge/manifest.json DOES contain this exact
rejected object. Its source-import graph has177 descendants:174 retained
predecessors plus R1SemanticPrefixAgreement, R1SemanticPrefixCompletedAgreement,
and R1SemanticPrefixCutAgreement. Their current-source correspondence is
provisional. The complete exact list is in circle-use-host.json. This177 list
is source-graph reachability, not a claim that177 actual build receipts were
inspected or that all177 must be replayed. Direct receipt impact, historical
source identification, and a bounded repair frontier need separate audit.

No Lean/build/replay occurred during this audit. audit-circle-use.py uses the
pinned existing header parser, reads only host sources/receipts, verifies all
direct receipt-object relations, and emits circle-use-host.json. The separate
local codec inventory is pinned by source path/hash.

Follow-up inventory: the177 affected source files are144below16KiB,32at16--64KiB,
and one86,989-byte HenselIntegralLift file; none exceeds256KiB. No explicit
generated-certificate marker was found, which is not evidence that these
algebraic proofs are cheap. prefix-frontier.json records size/shape flags for
every affected module and pins all three actual successful receipt sources.
Their direct imports and recorded object hashes are verified, while paths
from those imports to Circle are explicitly source-graph evidence.

A retained Aug24 Lake trace and candidate pre3638d7546 source were found beside
the exact rejected object. The trace has64-bit Lake source/output hashes,
not a SHA256 producing-source receipt; these have not yet been recomputed.
historical-candidate.json keeps the identification provisional.
