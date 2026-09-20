# R17 universal compatible raw/final interpolation

Date: 2026-09-21. Base `786f1a8e4d336fd33cd8e596e1da6fb0e2cb1eaf`
plus this changeset. No production protocol change.

## What is proved

`RawFinalCoverage.lean::compatible_raw_final_coverage` constructs four
polynomials a,b,c,d for any n distinct fibre roots and prescribed final
polynomial F of degree below m, with n<=m. The target four values at each
fibre must satisfy the existing source-shaped four-slot fold equation
with F at that fibre. Nonzero x,y and characteristic not 2 are explicit.
There is **no exclusion on alpha** and no generic-rank assumption.

The construction first inverts each four-slot target, using the retained
R16 butterfly inverse. It interpolates b,c,d to degree below n, then sets

`a = F - alpha*b - alpha^2*c - alpha^3*d`.

Compatibility makes a have the correct values at every fibre. Its degree
is below m and the folded polynomial equals F identically, not just at
the query points. This proves the reverse inclusion missing from the
earlier `FinalConsistency.lean` necessary-condition result.

For n=22,m=256, this covers the 88 raw quotient values and 256 final
coefficients subject to the 22 fold equations. The three nonconstant
channels have degree below 22. After conversion to the natural line basis,
the quotient's last three coordinates vanish, so the two quotient image
conditions hold. The maintained R16 natural-basis conversion supplies
the algebraic route; the new Rust test checks the actual selected basis
and encoder. No complete Rust-to-Lean execution refinement is claimed.

## Source test and preserved limitation

`r17_actual_prefix_raw_final_interpolation` reads each existing accepted
public-prefix record. It constructs compatible targets from a dense source
quotient, then independently interpolates the three low-degree channels
using the source Final256 evaluator's basis matrix. Its small solve is
checked against the original matrix by the retained pivot-inverse checker.

At each prefix it tests the actual alpha, zero alpha and minus the first
fibre's y coordinate. The last two avoid silently relying on convenient
generic fold coefficients. It checks all 88 raw quotient values using the
actual encoder, all 256 final coefficients, the quotient image conditions,
both OOD zeros of Lq and the actual encoded product Lq at the raw locations.

An explicit negative control verifies that the recovered original message
changes active H1 rows. Therefore **this is not a legal-H1 coverage proof**.
The construction also does not preserve G semantic/point/relation values.
The two source tests supplement the universal polynomial theorem; they
are not its proof and are not a new complete privacy test.

## Next reduced obligation

Update: `R17_RAW_FINAL_KERNEL.md` proves the polynomial divisibility
characterization below and tests an explicit source kernel basis. General
coverage of the remaining H1/G maps remains open.

Instead of treating raw and final values as independent targets, start
with this compatible interpolant and correct the remaining observations
inside its raw-zero/final-zero kernel.

Let P(t) be the product of (t-t_i) over the distinct queried fibre roots.
For a zero final polynomial, the candidate kernel description is

`b=P*B, c=P*C, d=P*D, a=-alpha*b-alpha^2*c-alpha^3*d`.

This uses the same coins; it does not create fresh masks after disclosure.
The full source quotient image still imposes its two high-coordinate
conditions. Deriving this kernel description and its exact source basis
is the next concrete step. The expected full quotient-kernel dimension
is 1022-(88+256-22)=700; that dimension statement is not a new compiled
rank theorem in this change.

The remaining H1 active-row/balance/point constraints and G semantic/point/
inactive/first-relation constraints must be solved in that kernel, with
universal coverage or explicit exceptional-event bounds. The C1 joint
coverage, commitments, adaptive shared oracle, seed expansion, visible
failures/retries/publication and malicious-prover soundness remain open.

## Exact evidence and failures

Lean uses the existing `/Users/dominic/ZK/AspisFormal` workspace and local
r17/r16 object directories. The initial invocation discovered a missing
`FinalConsistency.olean`; that small dependency was compiled explicitly.
The next invocation hit the 1800 MB cap. Inspection found the already
recorded `FibreInterpolation` predecessor used about 2 GB and cap 2600 MB
(`R16_UNIVERSAL_RAW_ARGUMENT.md`); no large numeral/recurrence is evaluated
here. The cast proof was simplified from `exact_mod_cast` to a direct
WithBot order lemma, then the focused leaf compiled with `-j1 -M2600`.
There was no unchanged retry with successively larger memory caps.

Final `#print axioms compatible_raw_final_coverage`: propext,
Classical.choice, Quot.sound; no sorryAx. The restored FinalConsistency
dependency reports the same standard set for both declarations.

Rust commands were offline/locked/release/jobs=1, package `aspis-prover`,
`--lib r17_actual_prefix_raw_final_interpolation -- --ignored --nocapture`,
with `ASPIS_R17_PUBLIC_PREFIX_LOG` selecting the checked-in world0/world1
record. The first compile found an unsupported `M31.square` call; replacing
it with multiplication fixed it. The next source change added the explicit
active-row negative control, justifying the final rerun.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Initial Lean attempt, missing dependency object | 1 | 6.59 | 669548544 | 0 |
| FinalConsistency cache restoration | 0 | 8.54 | 1382465536 | 0 |
| RawFinalCoverage at 1800 MB cap | 134 | 7.78 | 1927839744 | 0 |
| RawFinalCoverage simplified proof, 2600 MB cap | 0 | 10.15 | 1992015872 | 0 |
| Rust first compilation, method typo | 101 | 3.01 | 406798336 | 0 |
| Rust world0 initial successful construction | 0 | 23.78 | 522797056 | 0 |
| Rust world0 with active-row negative control | 0 | 23.19 | 514818048 | 0 |
| Rust world1 with active-row negative control | 0 | 0.45 | 81166336 | 0 |

All timings use `/usr/bin/time -l`. Accepted Rust runs each report one
test passed and zero failed. No host proof regeneration or unchanged full
suite was needed. Logs under `/tmp/aspis-r15-host.drHYn9`:
`r17-raw-final-coverage-lean{,-v2,-v3}.log`,
`r17-final-consistency-cache.log`, `r17-raw-final-world0{,-v2,-v3}.log`,
and `r17-raw-final-world1.log`. Earlier failures remain recorded.
