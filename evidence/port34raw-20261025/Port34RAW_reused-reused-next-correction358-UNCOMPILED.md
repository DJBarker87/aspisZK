# Proposed correction after358 — UNCOMPILED, no359 authority

The concrete chosen-context replay is rejected; it cannot be called compatible.
Do not retry358 unchanged. No new compiler, host, extraction or selection scan
was used after failure. This proposal is not a new theorem or revised selection.

## Actual rejected application and visible statement difference

The full kernel diagnostic is retained in kernel-obstruction358.txt and stdout.
It rejects Query31SourceSchedule.queries_success_pairs_functional_full from
CURRENT:INCREMENTAL:Query31SourceOracleBridge:part0 at its Exists.casesOn application
of queries_success_with_digest_pairs_full from
CURRENT:INCREMENTAL:Query31SourceCalls:part0. The common existential variables,
absorb/decode/after equations and eight-pair bound agree in the printed diagnostic.
The argument's printed suffix is:

```
pairs.length = 8 ∧ stateChain pairs ∧ materializedOutputs pairs blocks advances
```

The eliminator expects:

```
pairs.length = 8 ∧
(∃ first rest, pairs = first :: rest ∧ first.state = absorbed.state) ∧
stateChain pairs ∧ materializedOutputs pairs blocks advances
```

These are printed application types in the existing local binder context, not
standalone declarations. Full reference statements and proof bodies are saved
additively as reference358-Query31SourceCalls/OracleBridge.lean.txt, from immutable
published d346dc7cb7 evidence blobs; exact revision/path/hash/size are in result358.
Their association to the currently chosen raw bodies is NOT established by source
text. In particular, the reference Calls statement already contains hfirst,
while the actual selected Calls declaration's diagnostic type does not.

Proposed repair: reconstruct the actual strengthened Calls theorem from its
successful source-call decomposition with the original binders and hypotheses,
then recheck the actual dependent OracleBridge proof in that coherent context.
The reference proof constructs exactly pair0..pair7. Its first-state witness is
`⟨pair0, [pair1, pair2, pair3, pair4, pair5, pair6, pair7], rfl, rfl⟩`.
This symbolic finite-list shape is the direction to prove, rather than normalizing
large arithmetic or adding a head-state/output-equivalence hypothesis. The
successful query equation remains the input; the head-state fact must be a
conclusion derived from the same source execution. This is not derivable merely
from arbitrary nonempty list length and adjacent stateChain. Do not assert a
wrapper over the weaker chosen theorem supplies the missing execution anchor.

No source theorem/premise has been changed in this job. Any new source-derived
proof or origin choice needs explicit provenance/closure assessment, preserves
all other fields, and is a NEW re-pin, not the same historical declaration.
The current13/45/4 choice policy remains unchanged in358.

## Separate operational blocker

There are26 PANIC lines for13 distinct normalized private-name collision pairs.
Pinned Environment.lean:459–468 normalizes privateToUserName into AsyncConsts'
trie; addDeclCore:701+ also registers checked declarations into that trie. Exact
private Names from multiple modules can therefore collide in the elaborator
metadata despite differing actual Names. These failures were retained, not ignored
as a successful replay. No explicit Name renaming, first-wins drop, comparator
weakening, unchecked logical insertion or trust-import is an acceptable repair.
A future normal-checking reconstruction must support the original private Names
and their strict CIs while handling the elaborator metadata coherently. No safe
implementation of that change has been validated here. Fixing the Query31 type
mismatch alone does not establish that this independent issue is resolved.

Future actual consumer still must replay original parse_header's full old Bool
application context, SDK/S1/D189, the complete concrete theorem, then exact
readback/import/primitive/constructor/recursor/standard-axiom audits. No target,
artifact binding or adaptive security conclusion follows from this proposal.
