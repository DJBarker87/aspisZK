# R17 balanced raw/final kernel

Date: 2026-09-21. Base `e9a26a95` plus this changeset.

## Universal chord algebra

For distinct unit-circle points (x0,y0),(x1,y1), set
`b=y0-y1`, `c=x1-x0`. `ChordBalance.lean` proves `b^2+c^2 != 0`
over any field of characteristic other than two. The proof uses the
dot/cross identity: a zero squared normal would force dot=1 and cross=0,
then equality of both coordinates. It does not assume ordered fields,
positive definiteness or a random nondegeneracy event.

The same leaf proves that, given the quotient image equation
`b*v-c*u=0`, the balance equation `b*u+c*v=0` is equivalent to u=v=0.
It also proves the special direction's balance identity
`b*(b*t)+c*(c*t)=(b^2+c^2)*t`.

## Source application

For the source chord product and q[1023]=0, its coefficient at 1023 is
`b*q[1021]+c*q[1022]`. The transport defines that coefficient as the sum
of original inactive rows. The strengthened test checks these identities
on every one of the 700 explicit kernel directions, against the actual
chord product and inverse transport.

The first 699 directions have all three high quotient coordinates zero
and therefore inactive balance zero. The last direction has balance
`(b^2+c^2)*leading(P*t^233)`, which is nonzero. Thus it controls the
balance scalar independently of the 699 balanced directions. No extra
normal-zero exceptional event is needed for distinct source circle points.
Sampler failures and source field/index refinement remain separate.

This leaves the balanced kernel with three channel polynomials
`bChannel=P*B`, `cChannel=P*C`, `dChannel=P*D`, where each multiplier has
degree below 233 for the 22-query, 256-coefficient profile. The folded
channel a is determined. The source test retains the increasing-leading-
coordinate independence check and all earlier raw/final/OOD controls.
The combined natural-basis, degree and dimension statement is not yet a
single compiled source refinement theorem.

## Remaining reduced maps

Dropping only the nonbalanced direction and balance row gives:

- H1: 214 active-row and three point constraints, 217 rows.
- G: 271 semantic coordinates, three point values and six compact
  relation coefficients, 280 rows with the two retained compatibility
  equations.

Both source prefixes have ranks 217 and 278 respectively. Original-matrix
pivot-inverse checks verify these finite results, and the old 218/279
checks on the full kernel remain in place. Neither result establishes
universal rank. The first remaining source proposition is coverage of
these active/point and semantic/point/relation maps on the 699-direction
balanced kernel for arbitrary eligible prefixes, with explicit exceptional
event bounds where required.

No production protocol path, mask distribution or negative regression
changed. C1 joint coverage, commitment/oracle/seed behavior, failures,
retries/publication and malicious-prover soundness remain open.

## Exact focused evidence

Source revision `e9a26a95c2315dc422a19e0c411aa5c4f45ac875` plus this change.
Lean used the existing `/Users/dominic/ZK/AspisFormal` cache, r17/r16
object paths and `lake env lean -j1 -M1800` with explicit root/output.
The first two axioms audits list propext/Classical.choice/Quot.sound;
the special-direction identity lists propext/Quot.sound. No sorryAx.

Rust used the cached offline/locked/release/jobs=1 command for
`-p aspis-prover --lib r17_actual_prefix_factor_kernel_reduced_maps
-- --ignored --nocapture`, selecting each checked-in public-prefix log
through `ASPIS_R17_PUBLIC_PREFIX_LOG`. Compilation and the named reduced
eliminations remained small local jobs; no heavy generated replay ran.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| ChordBalance.lean | 0 | 9.20 | 1362034688 | 0 |
| Balanced-kernel world0 | 0 | 29.88 | 542081024 | 0 |
| Balanced-kernel world1 | 0 | 4.93 | 80969728 | 0 |

Metrics use `/usr/bin/time -l`. Each Rust invocation reports one test
passed and zero failed, with test runtimes 4.81 and 4.66 seconds.
Logs under `/tmp/aspis-r15-host.drHYn9`: `r17-chord-balance-lean.log`,
`r17-balanced-kernel-world0.log`, `r17-balanced-kernel-world1.log`.
No host proof regeneration, unchanged full suite or formal release replay
was needed for these focused changes.
