# Reusing the masked semantic core

The new sources `SemanticTransport.lean` and `MaskedSemantic.lean` connect
the R1 opening candidate to the existing `R0P.Mask` algebra. Both compile
on the pinned NUC runner. The combined import and axiom audit,
`R1SemanticReuseCheckpoint`, passed in 1.65 s at 4,041,956 KiB peak RSS,
with zero swap and only `propext`, `Classical.choice`, and `Quot.sound`.
This is a checked deterministic implication, not a final security result.

`SemanticTransport` fixes the point triple to alpha, its polynomial binary
successor, and its bit-2/3 toggle. It applies the existing coordinate reversal
and coefficient-to-row transport. The opening's three point claims then
become exactly `honestClaims`; claim family 3 becomes `honestExtra` with the
existing Libra row. The existing candidate descent supplies `BaseTyped`
for lanes 0–25, using the explicit common-subfield premise.

`MaskedSemantic.candidate_semantics` applies the existing concrete mask-degree
theorem, `checksAcceptZ`, `originalTotal_zero_of_masked_accept`, and
`semantic_of_total_zero`. Its final extraction uses the existing
`semantic_extraction` and `extraction_step`. None of their premises is
weakened or replaced with a new assumed semantic conclusion.

`large_matching_extracts` obtains a candidate from the actual R1 opening
theorem when its matching support has at least 9,558 positions. It derives
the honest point/Libra checks and row typing, then applies the masked core.
Its six semantic exclusions are explicit: LogUp, theta, zerocheck, mu, eta,
and alpha. They are required for every candidate in the literal R1 list,
whose existing bound is 100. Candidate uniqueness is not required.

The conclusion retains membership in that list, production constraints,
copy-link balance, and `InputNoteExtracted`. That last relation contains an
input-note secret/salt/path matching the public nullifier and anchor. It is
not a theorem for the entire settlement, output-value/range requirements,
or privacy.

The connection is an E-valued field model. The source's K-valued point and
Libra construction followed by K-to-E embedding, parsed accepted checks,
committed-word typing, public-input typing, and concrete packing basis
still need implementation correspondence. The inactive and circle rows
remain explicit inputs to the opening theorem. The new 33-round transcript
must supply and bound the exclusions with the correct message timing and
actual samplers; the old 32-round D3/Fiat–Shamir theorem is not applied.
Neither shared-oracle Fiat–Shamir security nor a simulator follows from
this deterministic candidate-level implication.

The subsequent [`SEMANTIC-PREFIX-BRIDGE.md`](SEMANTIC-PREFIX-BRIDGE.md)
checkpoint now derives these candidate-level exclusions from the first 25
parsed semantic rounds. It reuses the old padding and prefix lemmas and
proves exact equality of the R1/R0 candidate predicates. The old per-prefix
sampler bounds therefore refer to the same model events. Source
correspondence and the new shared-oracle instantiation remain open.
