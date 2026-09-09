# Four cubic evaluations in an arbitrary submodule

`FourPointSubmodule.lean` is kernel-checked. It supplies the deterministic interpolation interface needed by the denominator-cleared chord argument:

For a field `K`, any `K`-module `M`, a submodule `S`, four fixed vectors `w0,…,w3` and four pairwise-distinct field elements `a`, if

```
w0 + a • w1 + a^2 • w2 + a^3 • w3 ∈ S
```

at each of those four elements, then every `wj∈S`.

The field may have any characteristic; interpolation points may include zero. No basis, finite-dimensionality, independence of the coefficient vectors, nonzero-coordinate assumption or previous coefficient membership is needed. The same coefficient vectors and same submodule are used throughout the four evaluations. This is not a conditional-sampling, arbitrary-oracle recovery or verifier-acceptance theorem.

## Reuse rather than a new interpolation proof

The earlier green `ExactFoldRecovery.four_code_evaluations_recover_coefficients` proves coordinate-word membership by Lagrange interpolation. Its target is a submodule of `Pos→K`. The new leaf transports an arbitrary target `S⊆M` into that setting:

1. Construct the actual linear map `combine:(Fin4→K)→ₗ[K]M`, taking `c` to `Σj c_j•w_j`.
2. Pull `S` back through this map, yielding a submodule of `Fin4→K`.
3. Apply the existing theorem to the coordinate polynomials `X^j`, each of degree at most3.
4. Their degree-`j` coefficient vector is the `j`th unit vector; applying `combine` gives exactly `wj`.

Both linearity and this last unit-vector identity are proved. There is no assumed inverse matrix or unverified equality interface. The file exposes a four-element `Finset` interface, an injective `Fin4→K` interface and the literal scalar-power corollary `literal_cubic_four_points`.

No old V5 work-normalised error is imported into a security budget. Only the maintained deterministic interpolation lemma is applied; unrelated modules in its verified import closure supply no new numerical claim.

## Focused evidence

Research HEAD: `edb199c12fcc41f00330298b95b4736f60ac6f3a`. Borrowed source closure: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. The existing `ExactFoldRecovery` source/olean hashes are checked before and after the new leaf. Concurrent main HEAD is recorded but its newer work is not imported by assumption: each borrowed source is checked against the stated older pin.

| Check | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| [v1](experiments/four-point-submodule-v1.log) | 1 | 7.66 s | 5,493,882,880 B | 0 |
| [v2](experiments/four-point-submodule-v2.log) | 0 | 13.42 s | 5,604,425,728 B | 0 |

The first attempt had two local elaboration errors: the identity ring homomorphism needed explicit simplification in the scalar-map law, and `Fin.val_three` is not a declaration in this cache. The changed source uses `RingHom.id_apply` and the literal small fact `(3:Fin4).val=3`. The mathematical statement and all premises are unchanged. The rejected diagnostic's temporary `sorryAx` is absent from the green audit.

All five final audits contain only `propext`, `Classical.choice`, `Quot.sound`; no added axiom or `sorry` occurs in retained source. Source SHA-256:
`4ef195e244877b485ffb7929aa58fb85ec0512e54ed40a269dfa9e0867be4037`.
Olean SHA-256:
`55163f124053b9e89f40c52c42e0269ba86446422b4b3844d2ef9e06c2f32fc6`.

The reused interpolation source hash is `cec5a14467730d504a1d907a97171c629695a378266d701296c0d0206fbf64a6`; its olean hash is `a04a1ef54343ab2b884302a71883c1f789ff9dddd9b5dbb696b43406465dc7d6`. Lean4.32.0 is pinned at `8c9756b28d64dab099da31a4c09229a9e6a2ef35`; Mathlib is `81a5d257c8e410db227a6665ed08f64fea08e997`. Both checks used the serialized build slot, `-M7000` and the7,340,032-KiB aggregate child-process RSS guard. No dependencies were rebuilt, and no Rust/SBF/runtime experiment was run.

Archived exact command:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_four_point_submodule.sh \
  docs/research/v8-no-work-100-20260907/experiments/four-point-submodule-v2.log
```

The runner requires a fresh log filename for a justified changed-source check. This proof changes no protocol message, proof-body byte, accepted check or production setting. Applying it to the concrete denominator/membership submodule and the causal chord game is the consuming theorem's separate task.
