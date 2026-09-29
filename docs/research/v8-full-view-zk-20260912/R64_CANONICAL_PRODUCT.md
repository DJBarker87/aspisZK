# R64 arithmetic bridge — generated execution still pending

Base `2a9d914ff615bfc9d046399074d05b8164791412`, same isolated branch
`research/v8-r64-guarded-m31-20260929`. This follows the
[extraction checkpoint](R64_EXTRACTION_CHECKPOINT.md); it does not complete
the optimized generated inverse proof.

## Verified result

`CanonicalProduct.lean` adds **nine compiled arithmetic theorems** using the
retained `RawReducerNat` definitions and symbolic bounds:

1. Two canonical operands have product below P².
2. For n < P², one mask/shift fold is below 2P.
3. One conditional subtraction therefore gives a canonical result.
4. That result is n modulo P.
5. The retained negative at n = 2⁶²−1 yields the noncanonical value P,
   although its residue is zero. Merely assuming n < 2⁶² is insufficient.
6. For **all pairs of U32 values**, the complete guarded natural-number
   formula (one-fold canonical branch, original reducer fallback) equals
   the old raw multiplication formula.
7. That guarded formula equals the product modulo P.
8. Its output is canonical for all such inputs.
9. In the canonical branch, the product fits U64, the folded sum fits U32,
   and the conditionally subtracted output is below P.

The general theorems use symbolic inequality/modular arguments. Only the
single small negative expression is evaluated concretely; there is no
enumeration, large recurrence normalization or fresh inverse assumption.

**Scope:** these are natural-number arithmetic and width facts. They are not
yet execution theorems for the freshly generated R62 multiply. In particular,
the checked-word operations, branch evaluation, cast placement, generated
fallback and composition into the inverse loop still require the extracted
code. The natural-number model must not be substituted for that source proof.

## Focused local fallback and evidence

Repeated SSH attempts over both NUC Tailscale addresses failed. No NUC job
was restarted. The laptop had the exact Lean 4.32 toolchain and a compiled
mathlib cache at `81a5d257c8e410db227a6665ed08f64fea08e997`, so only the tiny
Nat-only predecessor and changed leaf were checked locally. No dependency
build, full Aeneas runtime import or heavy job was started on the laptop.

The first local check compiled the missing `RawReducerNat` object and the
initial five-theorem draft. After adding the four guarded-formula/width
theorems, only `CanonicalProduct` was recompiled; the unchanged predecessor
object/log was reused. Both checks succeeded.

Final retained evidence:

| Target | Exit | Wall | Peak RSS | Swaps | Axioms reports |
|---|---:|---:|---:|---:|---:|
| RawReducerNat (retained dependency) | 0 | 11.53s | 436,371,456 bytes | 0 | 4 |
| CanonicalProduct | 0 | 4.10s | 772,702,208 bytes | 0 | 9 |

The new leaf's peak RSS is approximately 737 MiB. The runner used
`lake env lean -j1 -M1024`, a 30s/35s soft/hard CPU limit and a 60s wall limit
per command. No process hit those limits. Every new theorem has an axioms
audit; only standard `propext`, `Classical.choice`, `Quot.sound` occur, with
no axioms at all for `product_lt`. No `sorryAx` or additional axiom occurs.

Exact source hashes, base revision, commands, toolchain and resources are in
`evidence/r64-canonical-product`. Verify without replay:

```
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r64_bound_evidence.py
```

The committed `run_r64_local_bound.py` supports `--reuse` for focused checks.
The separate NUC runner draft remains local and unverified.

## Exact next action and unchanged larger boundary

When the NUC reconnects, inspect `aspis-r64-bound-a.service` and its output
before launching anything. Fetch and audit the **already completed** R64
extraction at `/home/dombarker/project-offloads/aspis-r64-extracted-20260929-a`;
do not repeat it unchanged. Compile the smallest new generated leaf and apply
these bounds to prove equality with R63's generated two-fold multiplication.
Then transport equality through the actual inverse loop, before the
CM31/QM31 inverse and sampler composition.

The generated artifacts have still not been retrieved. Full-transcript
privacy, shared-oracle/seed/commitment behavior, observer disclosures,
failure/retry/publication laws, quantitative losses and separate coherent
pre-beta extraction soundness remain open. No local arithmetic result closes
those gates or changes the C1 negative regressions.

No runtime change or SBF rerun: CU remains **1,497,377 / 1,498,764**, with
both actual 1M-cap runs exhausting. No merge, deployment or wallet operation.
