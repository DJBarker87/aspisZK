# Validation evidence

## Pack and Python

- All 79 supplied pack files passed `shasum -a 256 -c
  PACK_SHA256SUMS.txt`.
- `tools/verify_repo_sources.py` verified all 18 pinned Git objects.
- Direct command `PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s
  tests -v`: 24 tests passed in 5.517 seconds.
- The unchanged wrapper
  `python3 tools/run_checks.py --stage python --output ...` failed before
  running tests with `subprocess.SubprocessError: Exception occurred in
  preexec_fn` on macOS/Python 3.12. That failure is retained and is not a
  wrapper pass.

## Actual Rust encoder

Isolated copied source:
`/private/tmp/aspis-v8-raw-repro-20260912.BQGqWh`.

Command:

```text
/usr/bin/time -l cargo test --offline -p aspis-prover --release \
  repaired_mask_map_has_this_annihilator -- --nocapture
```

Result: exit 0; one passed; test runtime 0.09 seconds; wall 16.20 seconds;
peak RSS 573,046,784 bytes; zero swaps.

The first preflight failed with Rust E0753 because an `include!`d harness
contained inner doc comments. Converting only those comments to ordinary
comments produced the passing run. Original encoder SHA-256:
`336d10034cb4a37140e5a3645eae7a76cf86a8b6cb2f0c4b8a213e97ac43bd54`.
Supplied harness SHA-256:
`7e68e0fdbac80a7c4bbf764287cc0ca76021d2ea621ade8c993cc463395124c8`.

## Valid positive-transfer trace diagnostic

Isolated copied source:
`/private/tmp/aspis-v8-raw-repro-20260912.BQGqWh`.

Command:

```text
/usr/bin/time -l cargo test --offline -p aspis-prover --release \
  diagnostic_q22_certificate_on_valid_positive_transfers -- --nocapture
```

Result: exit 0; one passed; test runtime 0.52 seconds; wall 35.54 seconds;
peak RSS 521,224,192 bytes; zero swaps. The focused test compiled the actual
honest pair-forest transfer compiler, actual mask builder/application, and
actual full circle encoder. The positive adapter's three-line overwrite was
repeated literally in the test because the generated experiment module is not
part of the prover crate.

The certificate has six nonzero coefficients and induces a 384-row semantic
functional. Its row-1014 coefficient is `170822063`. For each valid split
`(1,999)`, `(100,900)`, `(400,600)`, `(500,500)`, `(600,400)`, `(900,100)`,
and `(999,1)`, and deterministic mask seeds 1, 7, and 19, the test checked

```text
L(final column 3)
  = L(semantic column 3)
  + 170822063 * inverse(recipient_value * change_value)  (mod 2^31-1).
```

The pre-overwrite value varied across mask seeds; the final value was identical
across seeds for each payment. Full output is summarized in
`valid-positive-transfer-values.json`. The amount sweep recomputed the two
public note commitments, so it is not a same-public witness-pair experiment.

Instrumented honest-source SHA-256:
`c6007b630a414871dd927b0857496ae144fc2ed00bb59cc5010f08f24a8b779f`.
Instrumented encoder SHA-256 (including the earlier child certificate test):
`480841c8d490415a20ee357170297623b314504ce000a7458f5432e256633d3d`.
Cargo lock SHA-256:
`a1d2fc87435e98734f74a0fb1f070f1eaa5e5fe19266967092a7ea7849f8a91d`.

## Lean

Toolchain: Lean 4.32.0
(`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), repository-pinned Mathlib
artifacts, serial `-j1 -M1800`.

Validated retained-source revision:
`88081c690be32073eefdaad53b1b2821442ad46e`. The privacy sources in that
revision are the exact inputs to the final replay.

All thirteen generic leaves and the aggregate compiled from the retained
worktree sources. Maximum observed process RSS was 1,538,834,432 bytes for the
final aggregate replay; swaps were zero. The
exact `FSOracleExecution.lean` from `ab4f61fe...` (SHA-256
`aa2928cc4407c0cbe45910d0527a1cffa18e3a941698ee77fbc7910ffefd9806`)
compiled, followed by `FSProgrammingDraft.lean`.

| Target | Exit | Wall | Peak RSS | Swap | Artifact SHA-256 |
|---|---:|---:|---:|---:|---|
| `AspisV8Privacy.lean` aggregate | 0 | 1.03 s | 1,538,834,432 B | 0 | `d0c6f859d023d80c75e6b24f666987be68f8326dccfb9246a4deb3226ae78a84` |
| pinned `FSOracleExecution.lean` | 0 | 2.68 s | 667,353,088 B | 0 | `e7a9718f15626e27d9dfb9aacbe939e92984778b2c8b98c652edd75355582282` |
| `FSProgrammingDraft.lean` | 0 | 0.72 s | 645,185,536 B | 0 | `77e69ce28707eb63276ca6e3e6db5d072191e69ad422ca21029f4a92cfb4219a` |

Repairs preserved theorem statements:

- import the product additive-group instances;
- use the available BigOperators field import;
- replace removed `Mathlib.Data.Rat.Order` imports;
- spell the rational absolute-value triangle proof using `abs_add_le`;
- use a closed decision proof for the three small literal wire equalities;
- move the aggregate module comment after its imports.

`#print axioms` output contains only `propext`, `Classical.choice` and
`Quot.sound` where applicable; several results use fewer or no axioms.
There is no `sorryAx` in any successful compile. This reused cached imported
artifacts and was not an independent kernel replay.

An initial `lake env lean` invocation inside the fresh worktree attempted a
cold Mathlib clone and was interrupted immediately. The successful checks used
`lake env` from the existing pinned/cache-built `/Users/dominic/ZK/AspisFormal`
workspace with an explicit source root and temporary output directory.
