# Retry-mass arithmetic review

`experiments/RetryMassArithmetic.lean` proves the symbolic inequality needed
after an exact history-uniform nested-sampler law is available.  It does not
itself establish that law for the transcript source.

For a parameter space of rational cardinality `N`, let `w` be the exact mass
of every fixed accepted parameter under one bounded circle sampler.  Assuming
`2 <= N`, `0 <= w`, and total success mass `N*w <= 1`, the retained theorem
proves

```text
N*(N-1)*w^2*(1+w+w^2) <= 1.
```

Consequently, for any root set of cardinality `m` with `1 <= m <= N`, the
mass of a fixed ordered pair produced by the three-attempt distinct wrapper
is bounded by

```text
m*(m-1)*w^2*(1+w+w^2) <= m*(m-1)/(N*(N-1)).
```

Aborted ordinary decodes and exhausted retries are retained as zero mass;
there is no conditioning on success and no work/grinding credit.  The proof
is algebraic: `w <= 1/N`, and the full ordered-pair mass is at most
`1 - 1/N^3`.  Instantiating `w`, proving the history-uniform transcript law,
and connecting the nested source controller remain separate obligations.

## Focused evidence

The first NUC attempt failed only at an over-broad `positivity` invocation in
the final nonnegativity step.  It exited 1 in 3.06 seconds with peak RSS
6,671,428 KiB and zero swaps.  The retained source replaces that invocation
with an explicit nonnegative inverse-cube fact; no statement changed.

The second focused NUC attempt exited 0 in 3.34 seconds with peak RSS
6,705,408 KiB and zero swaps.  Both declarations audit to the standard
axioms `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or
new axiom.  It used Lean 4.32.0 commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`, `-j1 -M9500`, and the existing
NUC cgroup limits: 8 GiB `MemoryHigh`, 10 GiB `MemoryMax`, zero swap, and two
CPU cores.  Overlay provenance passed before and after compilation.

Hashes:

- retained Lean source: `089af987a928f39a32bc97eec2777b34a2d1cb707836b8196704371471743a8d`
- retained olean: `d7fc096153c20a9cb781feebe5f6b1195165b76367d5311c35491a27b31e0a7d`
- failed v1 source: `212c6217004ba2ba8c0bd3f6f580d54e745f5d99a333c83c1bf9444c5bb86e3b`

The exact commands, manifests, source snapshots, logs, and resource records
are retained beside the experiment as
`retry-mass-arithmetic-nuc-v{1,2}-*`.

## Security scope

This result is a reusable composition lemma, not a Fiat--Shamir theorem and
not a global V8 soundness bound.  It removes one possible retry-amplification
loss once the actual nested byte decoder is shown to have the assumed common
mass at every relevant history.  Fresh-oracle/ROM reasoning, adaptive OOD
answer absorption, the quadratic root bound, Halt/error routing, and the
accepted-extraction theorem remain open.
