# R17 factored raw-zero/final-zero kernel

Date: 2026-09-21. Base `5dbdc8f4566d72e28b74414328e36bae41e61bc5`
plus this changeset. No production protocol change.

## Exact polynomial theorem

`RawFinalKernel.lean` proves both directions of the kernel description.
Assume the folded polynomial is zero:

`a + alpha*b + alpha^2*c + alpha^3*d = 0`.

At each distinct fibre root t, the four raw values are evaluations of
`a ± y*b ± x*c ± xy*d`. With nonzero x,y and characteristic not 2,
all four vanish exactly when a,b,c,d vanish at that root. Let
`P(X)=product(t in roots, X-t)`. Lean proves that vanishing at those roots
is equivalent to divisibility by P. Combining these facts gives

`raw=0 and final=0  iff  P divides b,c,d and a=-alpha*b-alpha^2*c-alpha^3*d`.

The formal theorem takes the zero-fold equality as an explicit premise
and concludes the divisibility equivalence. It covers any finite root set
and every alpha. It does not assume rank or random challenge genericity.

## Source-basis construction

The new ignored source test builds P directly in the maintained natural
line basis using the retained `times_x` multiplication. It checks the 22
actual roots are distinct, and checks each P*t^j vanishes at them using
the selected Final256 evaluator. No large generated recurrence is reduced
and no 1022-column dense nullspace is constructed.

For j=0..232, it places P*t^j separately in each of b,c,d, with a chosen
to make the entire final polynomial zero. These give 699 directions.
The 700th uses degree 255 in the quotient channels with
`b = chord_b * P*t^233`, `c = chord_c * P*t^233`, `d=0`.
All directions satisfy q[1023]=0 and
`chord_b*q[1022]-chord_c*q[1021]=0`.

Each vector has a strictly later last nonzero coordinate than its
predecessor. These checked leading-coordinate facts certify independence
without an expensive dense rank calculation on the basis. A deterministic
linear combination is also checked with the actual encoder at all raw
locations, the chord product, both OOD evaluations and all final values.

The polynomial characterization is universal. Conversion to the complete
source quotient kernel, including its degree limits and image conditions,
is not yet a single compiled Rust-refinement/dimension theorem. The test
does not label its basis vectors legal H1 pads.

## Reduced maps, not a closed coverage gate

Update: `R17_BALANCED_KERNEL.md` handles the balance scalar explicitly
and reduces the remaining maps to the 699-direction balanced kernel.

The same source basis is projected to the remaining observations:

- H1: 214 active-row constraints, one inactive balance and three point
  values, yielding 218 rows.
- G: 271 semantic coordinates, three point values, one inactive balance
  and six compact first-relation coefficients, yielding 281 rows.

At both retained source prefixes, the respective ranks are 218 and 279.
The retained checker verifies a lower-rank pivot inverse against the
original matrices and the zero RREF remainder. G's two remaining
compatibility equations are still the terminal-coordinate and relation
evaluation equations; they have not been dropped.

This reduces the missing lower-bound problem to these two residual maps
on the factored kernel. It does **not** prove those ranks for every prefix
or supply an exceptional-event bound. The next source-specific proposition
is universal compatible-image coverage of these maps, beginning with the
actual active-row coefficient constraints. C1 joint coverage, source coin
law, commitments/adaptive oracle, failure/retry/publication and soundness
remain separate open obligations.

## Exact focused evidence

Lean: cached `/Users/dominic/ZK/AspisFormal`, local r17/r16 objects in
LEAN_PATH, `lake env lean -j1 -M2600` with explicit package root/output.
All three final `#print axioms` results contain only propext,
Classical.choice and Quot.sound, with no sorryAx. No full manifest replay.

Rust: `cargo test --offline --locked --release --jobs 1 -p aspis-prover
--lib r17_actual_prefix_factor_kernel_reduced_maps -- --ignored --nocapture`,
with `ASPIS_R17_PUBLIC_PREFIX_LOG` selecting the checked-in accepted prefix.
Time is spent in compilation and the named reduced-map construction/
elimination, not a schedule search or unoptimized arithmetic job.

The first Rust compile failed because the existing public-prefix helper's
kappa/tau fields were private to its test module. Their visibility was
extended only to the sibling research module, as was the existing natural
line multiplication helper. No field arithmetic or production API changed.
After success, an explicit source-root-distinctness assertion was added;
the final world0 run tests that source change, not an unchanged gate.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| RawFinalKernel.lean | 0 | 10.79 | 1791819776 | 0 |
| Rust initial visibility error | 101 | 2.68 | 400506880 | 0 |
| Rust world0 initial reduced maps | 0 | 27.23 | 559759360 | 0 |
| Rust world0 with root-distinctness check | 0 | 28.78 | 560267264 | 0 |
| Rust world1 with root-distinctness check | 0 | 4.04 | 80969728 | 0 |

Metrics use `/usr/bin/time -l`. Both final Rust runs report one passed and
zero failed; runtime test work took 4.46 and 3.78 seconds respectively.
Logs under `/tmp/aspis-r15-host.drHYn9`: `r17-raw-final-kernel-lean.log`,
`r17-factor-kernel-world0{,-v2,-v3}.log`, `r17-factor-kernel-world1.log`.
No original proof bytes were regenerated, and the C1/first-placement/
active-row negative regressions remain intact.
