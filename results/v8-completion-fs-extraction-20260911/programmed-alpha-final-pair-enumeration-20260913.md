# Programmed alpha final-pair enumeration bridge

The source-shaped compositions in
`FSV8ProgrammedAlphaFinalPairFreshEnumeration.lean` places a fresh accepted
alpha final-pair advance in the literal fresh-query enumeration of the same
factored whole-verifier run.  Candidate-to-whole history nesting is produced
from the programmed cut; it is not a caller-supplied interval.  Its ordered
strengthening places the complete fresh subsequence consumed by all rejected
pairs and the accepted pair as a `List.Sublist` of that same whole-verifier
enumeration.

`FSV8ProgrammedAlphaCandidateAlignment.lean` separately constructs the
candidate terminal alignment from the same programmed cut, the exact
pre-alpha/marker-continuation oracle equality, and the compiled candidate
script.  This removes candidate alignment as an eventual source-interface
assumption once the live successful challenge is identified with that
functional candidate result.

This is an intermediate deterministic bridge.  Cached alternatives and the
complete routed-event inclusion remain outside it.

Source SHA-256 values:

- candidate alignment:
  `59d00b4f8b0c5df6e164b29b34cbe0394f7a31eb01cafe3c1c9bf1d9b4ca1f95`;
- ordered whole-verifier enumeration:
  `aa0453f07100b98b53a78b702713dead0a007075465d511edcab0c4ca655ffd9`.

Focused replay on the Tailscale NUC used pinned Lean 4.32.0 and a user cgroup
with `MemoryHigh=7500M`, `MemoryMax=8G`, and `MemorySwapMax=0`:

```text
exit: 0
wall: 3.30 s
user: 2.19 s
system: 1.10 s
maximum RSS: 6,800,480 KiB
swap: 0
```

The final-pair leaf was rerun after its ordered strengthening:

```text
exit: 0
wall: 3.11 s
user: 2.25 s
system: 0.87 s
maximum RSS: 6,824,228 KiB
swap: 0
```

The candidate-alignment leaf also passed independently:

```text
exit: 0
wall: 2.93 s
user: 2.08 s
system: 0.84 s
maximum RSS: 6,768,124 KiB
swap: 0
```

The promoted theorems report only `propext`, `Classical.choice`, and
`Quot.sound`.  The retained source has no `sorry` or custom axiom.
