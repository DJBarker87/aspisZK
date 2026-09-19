# R15 actual sampler stopping and ideal event accounting

Date: 2026-09-19. Starting revision:
`0107b6531018948499703f740397d4fa18adfa06`.

## Literal source result

Target: `crates/aspis-core/tests/r15_q22_stopping.rs`, calling the unchanged
`Transcript::challenge_queries_without_replacement` at `(22, 2^18, 64)`.
Transcript source SHA-256:
`be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119`.

```sh
CARGO_BUILD_JOBS=1 /usr/bin/time -l cargo test --offline --release \
  -p aspis-core --test r15_q22_stopping
```

Exit 0; 3 tests passed. Wall 32.07 s including incremental dependency
compilation; peak RSS 398,934,016 bytes; swaps 0. Existing cfg/dead-code
warnings remain. No Lean file changed or compiled in this follow-up, so
`#print axioms` is not applicable. No full regression was repeated.

The deterministic mock hash streams check:

- A 22nd distinct value at draw 64 succeeds; the same value first appearing
  at draw 65 does not rescue an exhausted attempt.
- High 14 candidate bits are masked, and unused words of a consumed block
  are discarded rather than retained for the next transcript challenge.
- Success exactly at candidate 24 consumes **four**, not three, squeeze
  blocks. The next public challenge sees the advanced state after block four.

Inspection explains the last result: the `out.len() == count` check occurs
inside the word loop, after the outer loop has called `squeeze_block`.
For successful stopping candidate T, the number of blocks consumed is
`min(floor(T/8)+1, 8)` at this draw cap. Thus successful T in
{24,32,40,48,56} consumes an extra block; T=64 does not. This formula is a
source inspection conclusion with focused controls, not a Lean refinement.
Each block performs an output hash and an advance hash at the **same old**
state. A replay that stops immediately at the last accepted word is not
byte/state equivalent. The production behavior is preserved.

## Exact finite model, kept separate

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/r15_q22_exact_counts.py
```

Exit 0. Exact integer dynamic programming over `(distinct, pair-members)`
counts all 64-word tapes from `Fin(2^18)`, retaining failure and ignored
suffixes. Independent exhaustive enumeration checks two small domains.
Conditional on sampler success, the specified pair probability is exactly
`11/1636171776`. Failure mass has base-2 logarithm approximately
`-559.8342377093007`; the script prints the exact rational, as well as the
unconditioned pair-and-success mass. This calculation confirms that the
draw cap alone is not a meaningful exclusion mechanism for the known pair.

These are executable integer calculations, not newly compiled formal proofs.
IID candidate words are an explicit model premise. They are not inferred
from the mock hash tests, from SHA-256, or from conditioning away a private
oracle cache. The extra block changes later transcript state and still must
be included even when it does not change this model's returned schedule law.

## First remaining source proposition

The selected v4 host image has now been recovered and hash-authenticated
(`r15-q22-source-slice-audit.md`). Connect an entropy-backed
attempt and its **complete** shared-oracle history to this sampler and the
allowed public event. That refinement must include cached/prequeried output
and advance addresses, the extra block, post-query failures, caller retries,
and publication. The initial and v4 images are separately pinned; the
deterministic demo is not the intended entropy adapter.

The raw q4/q6 separator, ideal schedule probability, and actual publication
probability therefore remain distinct. In particular, no source-valid
numerical privacy advantage is asserted. If the joint event is reachable
with material mass, commitment hiding or earlier G surjectivity cannot erase
its plaintext statistic. A repair must suppress that disclosure, mask it,
or explicitly change the allowed leakage; no such protocol change is made.
