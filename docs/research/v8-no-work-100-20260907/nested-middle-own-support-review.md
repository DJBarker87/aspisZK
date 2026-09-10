# Nested middle own-support dichotomy

Status: kernel-checked as one focused leaf on the capped Tailscale NUC.
Source: [NestedMiddleOwnSupportDichotomy.lean](experiments/NestedMiddleOwnSupportDichotomy.lean).

## Exact result

Fix 29 distinct collected gamma nodes and four actual middle witnesses at
each node. The existing reconstruction determines one 29-component tuple
from the disclosed, alpha-adaptive finals. The new theorem
`early_member_or_all_nodes_bad` proves the following total deterministic
classification for that same tuple:

1. its componentwise own support has at least 38,228 original-code symbols,
   so its C1 projection belongs to `EarlyC1Family.family e.c1`; or
2. every collected gamma belongs to `SelectedOwnSymbol.badGamma` for that
   one tuple.

The right branch is derived using each middle witness's literal-family and
image-validity fields, the checked chord reconstruction, the 38,230-symbol
original support theorem, and the exact nodal reconstruction equality. It
does not assume candidate membership outside the witness, global received
polynomiality, or the disproved same-support recovery statement.

`claims_exact_and_support_classified` additionally proves that all 87
component point claims are exact for the same reconstructed tuple in both
support branches. These row equations are inherited from the repaired
ordinary-row gate; they are not added assumptions.

## Security consequence and remaining gap

This closes the deterministic classification that was missing after the
29-gamma by four-alpha reconstruction. The remaining support obligation is
now precise: bound the probability that an adaptive nested collector selects
29 gamma nodes all lying in `badGamma` of the tuple reconstructed from those
same nodes.

The existing fixed-tuple cardinality and joint query/alpha bounds cannot be
applied retrospectively, because the tuple is selected from the collected
nodes. Consequently this leaf books no new numerical error term and does not
claim global extraction. A valid next theorem must either couple this
post-selection event to a causal collector experiment or construct an
earlier fixed family with an explicitly charged cardinality. A union over all
possible reconstructed tuples is not justified.

Even the early-family branch plus 87 exact claims is not yet payment-witness
validity: the selected semantic/copy/note/path/output residual enforcement
and the concrete payment decoder remain separate deterministic/source
bridges. Fiat--Shamir restoration, authentication, and full-view ZK are also
unchanged open gates.

The result changes neither verifier messages nor proof bytes. The body census
remains 40,282 bytes, and no verifier-CU claim follows from this extractor
analysis.

## Focused verification

Only `NestedMiddleOwnSupportDichotomy.lean` was compiled. V1--v10 isolated an
elaboration recursion in a monolithic application of the already-proved
coverage theorem. V11 inlined that theorem's small symbolic steps and exposed
one ambiguous `own` name. V12 qualifies the selected own-support definition;
no theorem premise, imported proof, or resource cap changed.

V12 exited 0 in 3.20 seconds with peak RSS 6,875,692 KiB and zero swaps. Both
new declarations audit only to `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx` or new axiom. Lean 4.32.0 ran with
`-j1 -M9500` under MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0 and
CPUQuota 200%. Both 987-entry provenance checks passed with
`PROVENANCE_UNCHANGED=true`; no dependency or package replay ran.

Transport used `dombarker@100.108.41.90` over Tailscale. `nuc.local` was only
the pinned host-key alias. The runner retains research-cache pin
`289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; the per-run manifest pins the
exact leaf and imported blobs.

| Artifact | SHA-256 |
| --- | --- |
| Source / exact v12 source snapshot | `9c39f314b5dc3bbf436fce23f809ea0204960c5e2c0b6e7c64e20e50bf23d591` |
| Green olean | `68d18cc321ae0fc3a6e85275be22fa27fc0ce731a21c30efd81cd513a2927440` |
| Per-run manifest | `9ad02166279a5f2e4ed7763b299262293d973603a462e93f84d3fbed217c63bb` |
| Log | `b3a84fff1361f410dbec7cd4a7ad4c248ac0b80dfee1904df4d02a32f3add590` |
