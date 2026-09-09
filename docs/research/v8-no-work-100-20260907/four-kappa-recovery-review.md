# Four-kappa separation of the repaired ordinary rows

The kernel-checked leaf composes the same-quotient seven-alpha/three-tau construction with the literal shifted ordinary-row cubic. It targets deterministic recovery from a fork grid, not another probability estimate for a target selected after challenges.

The grid shares a fixed mathematical received word R, a common matching support S with `255 < S.card`, and the same original `Rows` inputs. There are at least four distinct kappa values, at least three distinct tau values under each kappa, and at least seven distinct alpha values under each kappa/tau. The tau and alpha node sets may depend on their earlier prefixes. Response0 depends on kappa/tau but precedes alpha; final256 may depend on kappa/tau/alpha. Each displayed actual carried prior is zero.

`four_kappa_common_support` constructs Q from the first kappa's three-tau subtree. Its agreement with R on S identifies every later adaptive final directly using the exact selected final-code overlap theorem. There are no separate Q_kappa objects whose equality is assumed. Each kappa's seven-alpha/three-tau algebra then establishes that kappa's actual corrected ordinary claim for this same Q.

The generic `four_corrected_claims` uses `ShiftedRowPrefix.before_prior`, whose affine transport identity was already proved from the source assembly. This is the actual error cubic

`inactiveError + kappa*row0Error + kappa^2*row1Error + kappa^3*row2Error`.

Four distinct zeros force that cubic to vanish, and the four errors are zero. The endpoint therefore proves all four literal `Rows.claimed j` equal their original functionals evaluated on `U = Rows.reconstruction Q + Rows.interpolant`. Inactive exactness is a conclusion, never a premise. Both image constraints for Q are also retained from the three-tau construction.

## Scope and remaining work

No Q, candidate membership, global received polynomiality, image validity or row exactness is supplied. The exact natural encoders, canonical four-slot folds, compact discrepancy boundaries and corrected row transport reuse the existing V7/V8 formalization.

The common matching support and zero-prior fork grid remain substantive mathematical hypotheses. This leaf does not obtain them from a Merkle root, one q22 transcript, actual verifier acceptance or a resource-bounded replay algorithm. It does not bound the mass failing to supply a grid. Its root arguments are deterministic interpolation after reconstruction, not invalid probability bounds for a post-selected Q.

Q is guaranteed to agree with the received word only on S. Correct batched ordinary rows and an image-valid Q do not by themselves recover all 29 original components or a valid payment witness. C1-before-early-challenge causality, component/OOD binding, actual authentication/replay access and tuple-to-witness constraints remain separate. This endpoint must be coupled to the collector's exact event/resource accounting before it supplies a global security bound.

## Evidence and cost

Source and runner are `experiments/FourKappaRecovery.lean` and `experiments/run_four_kappa_recovery.sh`. They use the existing laptop cache with Lean 4.32.0, `-M7000`, aggregate 7-GiB guarding and full imported-source provenance checks against research `532ade2064e533602902fc9ae5b4dd90f9207131` and immutable borrowed V7/source `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

The first focused replay, `experiments/four-kappa-recovery-v1.log`, completed with exit 0 including both provenance passes: 50.22 seconds for the Lean leaf, peak RSS 5,314,445,312 bytes, zero swaps. Both audited theorems use only `propext`, `Classical.choice` and `Quot.sound`. One unused-section-variable warning is nonlogical. There is no `sorry`, no new axiom and no unchanged replay.

Source SHA-256: `eecf3e62583bbd5f36ba60e0988fb5697fadb74cf80e276124b8b6ac97ce8853`.

Olean SHA-256: `06dd24b132cc6ab63052153b7fbb9115c05d428a4e3dcca8c8fb1f31762533fd`.

Runner SHA-256: `46c1c051f5307582675e98aff73820d1264dfdd624f7de093bc693c3382192b0`.

Concurrent main was read-only at `946ade6f86854c46b24a0291a5ce115749139a16`; every imported borrowed source still had to match the immutable `26a9` pin. Mathlib was pinned at `81a5d257c8e410db227a6665ed08f64fea08e997`. Source and runner are frozen after the successful replay.

Reproduction from the research root (the runner refuses to overwrite existing logs):

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_four_kappa_recovery.sh docs/research/v8-no-work-100-20260907/experiments/four-kappa-recovery-v1.log
```

Any justified future replay must use a new evidence filename.

No NUC job, package rebuild, production edit, protocol change or added proof-body value is involved. The 40,282-byte model remains unchanged. This is no proving/extractor-runtime, SBF or complete-transaction CU measurement, and no full-view ZK or Fiat–Shamir theorem.
