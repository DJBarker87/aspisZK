# R138: exact transcript primitive addresses

Source base: `c29d0a370a50f67667f38784b6c1e9eccec3e7a1`.

R138 begins the source-execution bridge left open by R137.  Against the exact
R137 Aeneas extraction it proves:

- transcript initialization at the all-zero state;
- the five labels used by the extracted `before_ood` callback;
- both the packed and long `Transcript::absorb` branches hash exactly
  `state || [DOM_ABSORB, label] || data`;
- `squeeze_block` hashes exactly `state || DOM_SQUEEZE`, returns that result,
  and advances to the hash of `state || DOM_ADVANCE`.

The focused Lean leaf compiles without `sorryAx`.  The extraction-only Rust
probe also checks the framing and the packed/long classification of every
payload shape in the pinned relation callback: four tests pass.  This probe is
executable source evidence, not a Rust-semantics theorem.

The packed proof factors the 192-byte temporary buffer into named symbolic
prefix, point-update, payload-window and populated-prefix lemmas; it does not
normalize all 192 cells.  The first remaining proposition is now the exact
R137 rejection sampler's bounded wrapping-index/source correspondence,
followed by its nonzero retry loop.  Full callback execution, sampler
admissibility, privacy, and soundness remain open.  No verifier source or
measured endpoint changed; the selected verifier remains **999,790 / 999,532
CU**.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r138_evidence.py
```
