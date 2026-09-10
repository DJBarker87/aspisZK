# Selected middle-support uniqueness

Status: kernel-checked on the capped Tailscale NUC, first attempt green.

Source: [SelectedMiddleUniqueness.lean](experiments/SelectedMiddleUniqueness.lean).
All eight axiom-audit declarations contain only `propext`,
`Classical.choice`, and `Quot.sound`. Only this new source and review
are owned by this change; existing green leaves are untouched.

## Mathematical endpoint

For the same arbitrary received word, two distinct actual natural1024 code
messages have total full-fibre support at most 262144 + 256. This is the
literal four-slot support used by `SelectedRegularLowSupport.fibreCount`,
not a new support correspondence premise.

Consequently two supports of size at least 200808 intersect on at least
139472 complete fibres, and their messages must coincide. The proof reuses
`NearGammaFibreBridge.full_fibre_overlap_le_256` and finite-set
inclusion-exclusion. No field enumeration, polynomial received word,
regular derivative, early-C1 success, or image premise is necessary for
the geometric fact.

`high_witness_unique` applies this fact to the actual `Witness` predicate.
Both witnesses retain their own image/row gates, literal family, actual
final fold, and retained higher-factor root. Their factors and their
kappa/tau/alpha histories may differ; only the execution and gamma agree.

## Canonical analysis object and timing

`MiddleWitness` adds the explicit interval 200808..252847 to an actual
`Witness`. `HasMiddle` existentially quantifies the quotient and all later
histories. `canonical` chooses one quotient if this proposition holds and
uses zero otherwise. Its existence and agreement with every high-support
witness are proved; the inactive zero has no witness claim.

This is a classical analysis object for a fixed execution and gamma. It
may inspect the whole strategy through its existential definition. It is
not claimed to be computable from a transcript prefix, available to the
adversary before later challenges, or an executable extractor. The actual
final continues to vary with alpha: `canonical_final` identifies it with
the alpha fold of this common quotient only on the stated middle event.

## Scope and remaining obstruction

This eliminates the need to assume a unique factor when forming one
middle-branch matching moment per gamma. It does not identify the factor,
bound the middle-gamma event, improve the 239599331 regular incidence
budget, add a sampler law, or prove payment extraction. In particular,
the 100-bit residual target remains open; a single higher factor could
still carry the entire current additive budget.

The numerical interval is an explicit predicate here. This leaf neither
assumes nor reproves that early-C1 absence and exclusion of Good imply the
upper endpoint. That separate source support partition remains the
consumer's responsibility.

## Focused verification

Only `SelectedMiddleUniqueness.lean` was compiled; no dependency or package
replay ran. Attempt `selected-middle-uniqueness-nuc-v1` exited 0 in 3.02 s,
with peak RSS 6,873,840 KiB and zero swaps. All eight axiom audits passed
with the standard axioms listed above. Both 975-entry provenance checks
passed; `PROVENANCE_UNCHANGED=true`. There were no failed Lean attempts.

Transport used `dombarker@100.108.41.90` over Tailscale, with `nuc.local`
only as the pinned host-key alias. Preflight found no active Lean scope
and 49.9 GB available RAM. The unchanged scope used MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0 and CPUQuota 200%; Lean 4.32.0 ran with
`-j1 -M9500`, module recursion 200 and 250000 heartbeats.

The preceding analysis began from research revision
`cc0414292fb7e99694eceecc5b28fc9cbc0a7012`; the new leaf was drafted and
compiled after local revision `24571219239106fd6c769f60ad7fb49725bef936`.
The inherited
isolated runner explicitly retains research pin
`289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 source pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; its per-run manifest separately
pins all appended green dependencies and this exact new source.

The frozen source snapshot, manifest, log and green olean were copied back
to `experiments/`. The compiler slot was explicitly released after the
terminal successful postflight; no further compiler job was launched.

| Artifact | SHA-256 |
| --- | --- |
| Source and `selected-middle-uniqueness-nuc-v1-source.txt` | `0c032f4f5bfca546929a8207e5acce44be80ad0e18e1d132f167533a4826cb3f` |
| `SelectedMiddleUniqueness.olean` | `ddfde95a34f41b0eea906cd91ea1d3ec7e3ea3f586e3e9a4169279fd497c5d9b` |
| `selected-middle-uniqueness-nuc-v1-manifest.json` | `8c1a0241f8b0e9828c75b0e075b0c5ef1e9ed275769f1b2707dda034759540ee` |
| `selected-middle-uniqueness-nuc-v1.log` | `1fb10c204d01e1d1e8dbdd271ff43509e270d544356b53362458a759228cc6f9` |
| Inherited `run_higher_y_nuc.sh` | `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52` |
