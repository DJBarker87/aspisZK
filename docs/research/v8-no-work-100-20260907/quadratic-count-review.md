# Quadratic specialization: checked quantitative consumer

Parent `289d7356c78a4cd493fe61a54f9548f2a0c11298`.

`experiments/QuadraticSpecializationCount.lean` now checks the following
implication. Let R be a polynomial in X over K[Z], let m>0, and bound every
X coefficient's Z degree by delta. For the nonzero fixed-size resultant
`E=Res(R, derivativeX R; 2m, 2m-1)`, if every gamma in a finite G has
`(Z-gamma)^m | E`, then `|G| <= 4*delta`.

The derivative coefficient-degree bound is derived, not assumed. The proof
reuses V7's `resultant_natDegree_le_of_coeff_natDegree_le` and the newly
checked determinant multiplicity counting lemma. It obtains
`m*|G| <= (4m-1)*delta <= 4m*delta` and cancels positive m symbolically.
No concrete-field enumeration or large generated numeral is involved.

**Scope:** this is the quantitative consumer, not yet the theorem supplying
its multiplicity premise for every actual square specialization. The actual
Sylvester kernel/basis composition, nonzero resultant, decomposition and
content/degree-drop exceptions remain necessary. The full proposed
`10*degZ(F)` branch bound remains unproved; no global error allowance is
claimed from this file.

## Focused evidence

All runs used the cached higher-Y scope on the NUC over Tailscale, with
MemoryHigh 8 GiB, MemoryMax 10 GiB, SwapMax 0, Lean `-j1 -M9500`.

| Attempt | Exit | Wall | Peak RSS KiB | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 3.18 s | 6,803,668 | 0 | Tactic expression parsing in coefficient helper |
| v2 | 1 | 3.45 s | 6,802,648 | 0 | Explicit natural-cast normalization needed |
| v3 | 0 | 3.26 s | 6,836,492 | 0 | Two standard-only axiom audits; provenance unchanged |

Command: `bash run_higher_y_nuc.sh <scope> QuadraticSpecializationCount quadratic-specialization-count-nuc-v3`.
Exact commands, snapshots and import manifests are retained for all attempts.

Source SHA256: `f726537f19ecf2a260ef22cfcbfe0e9c62a1739cb8aaa62bb76283ccac1e9398`.
Olean SHA256: `51e2b4e5e34a308cc4bf3196e1a316baf94f7963b8173f2105248630e9ef2771`.
Both final declarations use only `propext`, `Classical.choice`, `Quot.sound`.

No verifier, proof bytes, transcript or production configuration changed.
