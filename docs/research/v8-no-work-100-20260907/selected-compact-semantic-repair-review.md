# Compact semantic sumcheck repair

Status: **GREEN and frozen**. Checked target:
[SelectedCompactSemanticRepairV4.lean](experiments/SelectedCompactSemanticRepairV4.lean),
SHA256 `09e6970a14961ef17f5b2f8dd9455be5990302c7dc4bdb95b664878fea2b9c00`,
with eight standard-only axiom audits. Root launched the four focused checks
on the capped Tailscale NUC. V1–V3 remain immutable diagnostic sources.

## Exact source-shaped core

The leaf directly imports the already-pinned
`AspisFormal.V6AcceptedPathObligations`. Its `semanticParts`,
`semanticCoefficient`, and `semanticRunningClaim` retain the actual compact
grammar: 27 sent field elements per round, omitting coefficient one. The
linear coefficient is reconstructed from the incoming claim. There are ten
degree-at-most-27 polynomials; their boundaries and successor claims are
proved, not supplied as extra acceptance checks.

The new `ReferenceTrace table point` has ten reference polynomials, degree
caps, and the boundary recurrence starting at the Boolean sum of the SAME
table. It is intentionally an explicit mathematical reference, not an
authentication proof or a statement that its messages were fixed causally.

`repair_polynomial` derives a nonzero degree-at-most-27 difference polynomial
vanishing at the actual round challenge whenever the incoming claim
difference is nonzero and the outgoing difference is zero.
`badRound_card` gives the exact cap 27 in an arbitrary original finite
challenge domain, assigning an empty bad set to an identically zero
difference. `ten_step_repair` is symbolic finite induction, not normalization
of a concrete ten-round recurrence.

For nonzero eta and a reference trace for `mask + eta * real`,
`compact_unmasked_or_failures` returns exactly:

1. the Boolean sum of real is zero; or
2. the compact initial claim differs from the fixed mask sum; or
3. the compact terminal differs from the fixed reference terminal; or
4. some round repairs a nonzero incoming difference to zero.

This split applies to every compact transcript, so it applies to an accepted
subset without asserting that scalar acceptance authenticates the table.
The same eta is used throughout. Zero-eta rejection is an explicit premise.
Neither mask nor terminal authentication is inferred or silently removed.

## Reuse and causal boundaries

The exact compact boundary proof is a narrow source port of
`AspisFormal/Pool/V7CompactSemanticBinding.lean`; the reference/repair and
authentication split are ported from
`AspisFormal/V5AcceptedSumcheckSourceBridge.lean`. The reusable polynomial
representation and root counting come from the already-checked
`V5FriConcreteEncoderApplicability` and `JointImageGame`.

A local recursive import audit against the lane V2 manifest found thirty
unregistered V5 modules behind importing the complete old compact/adaptive
wrappers. This means absent from that manifest, not necessarily absent from
the remote filesystem. Root approved narrow source ports instead. No old
cache modules were staged, replaced, or replayed. In particular, the old
448-byte full-message framing is not used for the selected 432-byte compact
round. The old 25-lane/linear-helper probability bounds are not imported.

The next dependent leaf must connect `real` to the checked selected29
theta/equality-point/quadratic-helper table, then express a claimed and a
reference message plan depending only on earlier round challenges. It can
derive the ideal ten-step `270/|K|` repair bound by the V7 elementary adaptive
finite-mean induction. The final source-to-wire/decoder correspondence,
fixed-oracle construction, and fresh challenge law remain explicit. Labels
alone do not establish uniformity or freshness.

C1 precedes lambda and chi; C2 may adapt to both, but precedes theta, the
ten-coordinate equality point and mu. The initial mask claim precedes eta.
Round-i sent coefficients may depend on all earlier round challenges, but
not on challenge i. Later point openings remain adaptive, and their
authentication is precisely the terminal-failure alternative, not a frozen
future premise. No complete `310/|K|`, source acceptance, payment extraction,
or Fiat--Shamir claim is made by this core leaf.

## Frozen evidence

Research checkpoint parent: `125320408ae38060fab9c97391958025d353ce10`.
Inherited runner/cache parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`;
borrowed V7 pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Lean 4.32.0 used `-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0, CPU quota 200%, recursion depth 200, and 200,000 heartbeats.
No cap or heartbeat increase occurred. V4 passed both 1,063-entry provenance
checks with imported artifacts unchanged.

| Target suffix | Exit | Wall | Peak RSS KiB | Swap |
| --- | ---: | ---: | ---: | ---: |
| V1 (unsuffixed source) | 1 | 3.04 s | 6,661,956 | 0 |
| V2 | 1 | 3.08 s | 6,664,520 | 0 |
| V3 | 1 | 3.06 s | 6,665,556 | 0 |
| V4 | 0 | 3.33 s | 6,700,164 | 0 |

The first run found the wrong zero-evaluation API and deep elaboration at
generic applications and initial-difference reduction. V2 introduced named
degree/claim/membership helpers; V3 replaced a coefficient rewrite with its
typed symbolic equality and separated initial-claim reductions; V4 changed
only the initial Fin-index rewrite to `simp only` with `Fin.val_zero`.
No semantic statement changed. All eight V4 audits use subsets of
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
Unused-section-variable warnings remain harmless.

The exact attempt tags are `selected-compact-semantic-repair-nuc-v1`, then
`selected-compact-semantic-repair-v2-nuc-v1`, `...-v3-nuc-v1`, and
`...-v4-nuc-v1`.

| Version | Source/snapshot SHA256 | Log SHA256 | Manifest SHA256 |
| --- | --- | --- | --- |
| V1 | `ee2e57f2826b9dd7032592b18f2a0433d54464ed4da6c9528073d7825650ae64` | `87fe46c65638ca44f4911eb59e35710531bb817745578e1cbf513634c4aca978` | `d0b904ef6615694d5e8a7ed539cfe6afc31a221e51ff2e0a2f1baa4e0122ebbf` |
| V2 | `55019d583889111362f0508a8a9514b396578ac86cba7a36ca99352dae126410` | `26394f52208cf4fc39d57902eb74d8c4506e50fea6f307885d6d439a647e9e81` | `6e33672785fda3efe00194c4f41b7821f3ee0524469374a7043fb5ffd41b10d5` |
| V3 | `aaa35a6546753b9bf8cbd4133d9a04c313c1ed5c4ad02f952292e6ef7ba2202a` | `96aaa154514027d912a04cd55ead809be5484cda3aefedfb9d42b4641473a843` | `482ef290cb8783467814051b9b66e68267f416bf8292b8e9e7e81946e6a9eed9` |
| V4 | `09e6970a14961ef17f5b2f8dd9455be5990302c7dc4bdb95b664878fea2b9c00` | `e57f1ced015491b9cf10e1d495c7134b06c1b9c29aa078787969ce65d24eb9e9` | `24bd4eee6a51dffb0667326e90c61dc3924bed4236d0a0e115a3dda25c3ff1ba` |

Green olean SHA256:
`4069a9d57ee9360af289aa3a6713c6014979c53f9f25821738b40f3da2e23356`.
All sources/snapshots/logs/manifests are local. The ignored olean is locally
checked but optional for clones. Run the read-only
`experiments/audit_selected_compact_semantic_repair.py --check-recorded`
against `experiments/selected-compact-semantic-repair-evidence.json`; this
does not rebuild or replay anything.
