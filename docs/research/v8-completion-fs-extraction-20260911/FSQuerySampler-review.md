# Block-accurate query sampler source slice

Base inspected: `ab4f61feaca096ae3dae66e39d29f6e36bdca0ec`. No protocol,
format, verifier acceptance or production source edits.

## New checked endpoint

`FSQuerySampler.run_queries` proves, for arbitrary tape, initial oracle cache,
digest, accepted-candidate prefix, draw count and block fuel, equality of:

- running the chronological bounded query Script; and
- the literal block/inner-loop reference sampler's returned option, digest and
  complete oracle state.

`queries_valid` preserves constructed full-answer log/cache/first-exposure
invariants, including failed sampling. `scan_unstopped_draws` establishes the
symbolic advancement needed for the remaining loop-fuel adequacy proof.
`query_words_bounded` bounds every extracted candidate below 262144.

The local check is Lean **4.33.1**, not a historical4.32 or fresh-kernel replay.
The six-module Std-only source closure was rebuilt by `FocusedLeaves.py`;
pinned toolchain/Std artifacts were reused. Its temporary dependency artifacts
are deleted by that runner, so the focused repair rerun rebuilt those small
dependencies rather than using unmanifested `/tmp` artifacts.

Reproduce:

```sh
python3 docs/research/v8-completion-fs-extraction-20260911/FocusedLeaves.py --root FSQuerySampler
```

Successful evidence: `results/v8-completion-fs-extraction-20260911/FSQuerySampler-va1qzwiy/`.
Changed leaf: exit0, runner wall0.588705s; `/usr/bin/time -l` wall0.55s,
peak RSS693207040 bytes, zero swaps. Axiom lists contain only `propext` and
`Quot.sound`. Prior failed attempt retained at `FSQuerySampler-1qy8whvf`:
an insufficiently instantiated `run_squeeze` rewrite, not a changed theorem.

## Source-state boundary that must not be simplified away

Actual `Transcript::challenge_queries_without_replacement(22,1<<18,64)`
checks completion *inside* its eight-word loop. If the 22nd distinct query
arrives at draw24 (the last word of block3), the source squeezes block4 before
detecting completion; it consumes no candidate from that fourth block.
Finishing at draw64 performs no extra squeeze because the outer draw cap
already stops. A simplified per-word sampler can return the same positions
but the wrong digest and hash log.

`FSQuerySource.rs` executes the actual included `transcript.rs`, not a Python
copy, with synthetic coherent full-answer caches. It verified:

- distinct queries finishing at draw22: three blocks;
- finishing at draw24: four blocks, including the unused completion block;
- finishing at draw64: eight blocks;
- constant-output duplicate exhaustion:16 calls, only two fresh inputs;
- restoring the same initial state:16 additional cached calls;
- exact old-state squeeze/advance byte inputs and final digest in successful
  controls, including high masked-off word bits.

These are deterministic controls, not ROM probabilities or proof acceptance.
No secrets or witness material were used or printed.

Reproduce (binary outside the worktree):

```sh
rustc --edition 2021 -O docs/research/v8-completion-fs-extraction-20260911/FSQuerySource.rs -o /tmp/aspis-query-source-check
/tmp/aspis-query-source-check
```

Recorded compiler: rustc1.93.0 (254b59607 2026-01-19). Both commands exit0.
Compilation time0.98s/RSS160890880B/swap0; execution0.46s/RSS1589248B/swap0
from `/usr/bin/time -l`; logs in `results/.../fs-query-source-v1/`.
The unused legacy sumcheck KAT constant is the existing seven-field112-byte
shim; no sumcheck or payment code runs in this harness.

Source SHA256:

| Source | SHA256 |
|---|---|
| FSQuerySampler.lean | 4640b2f5273b977ec2986d658dd07af81864f090686c44fa9a4b57d5c08b72d5 |
| FSQuerySource.rs | e37db6e064559588a3be1027f063bb46099c48bee75c1844909a35d017db7dd4 |
| crates/aspis-core/src/transcript.rs | be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119 |
| crates/aspis-core/src/field.rs | 5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8 |
| crates/aspis-core/src/circle.rs | 8f6f0f32c8dd93e3ee459df0c1d0ef710b01996d3bc929dbeffb3f7d14a0227c |

## Remaining producer obligations

1. Prove the chosen block allowance adequate for the literal source loop,
   and successful output length22/distinctness; turn the result into the actual
   typed positions consumed by the selected Merkle suffix.
2. Prove literal Rust little-endian/AND equivalence to the bounded natural
   arithmetic used in `queryWords`, or use an actual translated-source bridge.
3. Produce the pre-query digest through the intervening selected semantic,
   OOD, image, row and first-fold transcript; absorb actual final256 and nonce.
   This file does not assign that digest retrospectively from desired queries.
4. Couple first exposures and cached/adversarial restarts to an explicitly
   bounded random-oracle experiment. No uniformity, independent retries,
   grinding credit or global security number is claimed here.

The useful next proof is block-fuel adequacy plus typed q22 schedule production,
then replacing the explicit schedule input at the same-body suffix boundary.
