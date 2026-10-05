# Question A: do the R941 conditions hold for every same-public witness difference?

Base `4e0f47381`, profile `AV8/R102/sparseG-bitperm-two-swaps/quadratic-channel-fold/merkle8-research-v1`.
Written for a reader who has not seen the repository. Lean names are theorems
in `docs/research/v8-full-view-zk-20260912/lean/`; node ids (P27, …) refer to
`lean/V8Audit/` in this directory, where each cited theorem is re-bound and
typechecked.

**Verdict: OPEN.** No separator survives in the diagnostics that could be
run, and no witness degree of freedom was found that violates a condition. Of
the three conditions, inactive balance holds for every witness difference
(on paper, from one source fact); exact image is equivalent to a coverage
statement that is unproved; the fold condition is not implied by anything in
the tree and requires a construction that has never been written or tested.
The stop condition did not trigger.

## 1. Setting

Field $\mathbb F_p$, $p = 2^{31}-1$, and $K = \mathbb F_{p^4}$. The trace has
1024 rows. The prover commits 29 columns: 16 semantic and 10 mask-only columns
over $\mathbb F_p$ (commitment C1), and three columns over $K$ (C2): the helper
$H_1$, the mask $G$, and $D$. A column $m \in F^{1024}$ is encoded as
$E(Tm)$, where $E$ evaluates the polynomial with natural-basis coefficient
vector $Tm$ on a circle domain of $2^{20}$ points, and $T$ is the public linear
map

$$(Tm)_j = m_{\pi(j)}\ (j<1023), \qquad (Tm)_{1023} = \sum_{r\in I} m_r .$$

Here $\pi$ is the two-swap order (`TwoSwapSourceTable.order`), with
$\pi(1023)=1023$, and $I$ is the set of 810 *copy-inactive* rows; the other 214
rows are *copy-active*. The domain splits into $2^{18}$ fibres of four points.

The published view contains: both roots; 699 field elements (initial claim; ten
semantic rounds; three point claims per column; the inactive sum
$\sum_{r\in I}(\text{batched column})_r$; two OOD vectors of 29 values at
circle points with parameters $u,v$; channel coefficients $p_0,p_2$; relation
rounds; the 256 coefficients *Final256*); 22 opening records, each all four
values of all 29 columns on one fibre, with salts; both frontiers; failures and
retries.

After $\gamma$ the columns are batched. The *ordinary channel* is the batch
without $G$. Its chord quotient $q\in K^{256\times 4}$ is the coefficient
vector with $L\cdot q = $ (batched coefficients), $L=a+bx+cy$,
$(a,b,c)=(1+uv,\,uv-1,\,-(u+v))$ the line through the two OOD points. The
*first fold* is $\mathrm{fold}_\alpha(q)_d=\sum_{s<4}q_{d,s}\alpha^s$, $d<256$.
Final256 is the first fold of the $\beta$-combination of the ordinary and $G$
quotients.

**R941** (`balanced_source_compatible_223_repair`, node P27). Let
$r\in F^{256\times4}$ satisfy

- (F) $\mathrm{fold}_\alpha(r)=0$;
- (I) $r_{1023}=0$ and $b\,r_{1022}-c\,r_{1021}=0$;
- (B) $\sum_{n\in I}\big(T^{-1}(L\cdot r)\big)_n=0$;

and let the normalised $223\times223$ determinant be nonzero. Then there is a
combination $x$ of 223 fixed directions with the same values as $r$ on the 214
active rows, the three point functionals and all seven ordinary relation
coefficients, with an arbitrary prescribed semantic pairing, and such that $x$
vanishes at all 22 query roots in all four slots, has zero first fold, zero
coefficients from index 1020, and satisfies (B).

The question is whether (F), (I), (B) hold for the vector $r$ that a legal
same-public witness difference produces.

## 2. Same-public degrees of freedom

Source: `crates/aspis-statement/src/pool_v1/` (`payment_relation.rs`,
`pair_trace.rs`, `pair_forest_trace.rs`, `pair_tree_profile.rs`). The public
transfer statement fixes pool, domain, anchor sequence and root, nullifier,
asset, recipient commitment and change commitment. The witness is: input note
(nullifier key, salt, value); pair leaf (first commitment, second commitment,
occupancy flag and inverse); `selected_second`; 20 membership siblings and a
leaf index; 3 super-root siblings and 3 private lane direction bits; recipient
and change notes (owner key, salt, value each).

| | Degree of freedom | Fixed by the statement? | Cells that change |
|---|---|---|---|
| D1 | `selected_second`, same commitment in both slots of one pair leaf | No | Row 913 (column 0), row 1017 (column 10); both copy-active |
| D2 | Same commitment at two leaves of one lane: index, 20 siblings, sibling slot and its occupancy cells | No | Path direction rows, sibling cells, every Poseidon block on the path; active and inactive rows, all 16 columns |
| D3 | Same commitment in two lanes: 3 super-root siblings, 3 lane bits | No | As D2 for the three super-root blocks |
| D4 | Input note key, salt, value | Yes, up to a Poseidon collision (nullifier and commitment) | — |
| D5 | Recipient and change openings; value split | Yes, up to a collision in the two public commitments | — |
| D6 | Derived cells: Poseidon states, occupancy inverse, $1/(\text{recipient}\cdot\text{change})$ at row 1014 | Functions of D1–D5 | — |

D2 and D3 exist whenever a note commitment was deposited twice. D4 and D5 are
empty computationally; a statistical claim over all valid witness pairs must
count collision witnesses, and these change cells arbitrarily. Every diagnostic
in the repository uses D1 only (`SAME_PUBLIC_ATTACK.md`; R84, R102, R546: "the
opposite selected input").

## 3. What the three conditions say

**Step 1** (Lean: `marker_pairing_eq_inactive_balance`, node P32). For every
$q$, $(L\cdot q)_{1023}=\sum_{n\in I}(T^{-1}(L\cdot q))_n$. So (B) says the
row-space vector of $r$ has zero sum over the copy-inactive rows.

**Step 2** (NEW ARGUMENT, dimension count). The coefficient vectors $c$ whose
polynomial vanishes at both OOD points form a subspace of codimension 2.
$q\mapsto L\cdot q$ is injective on the codimension-2 space (I) and lands in
it. Hence (I) holds for $r$ if and only if $r$ is the chord quotient of a
difference that leaves both OOD values unchanged.

**Step 3** (definition). (F) says the ordinary channel's own contribution to
Final256 is zero. Equality of the published Final256 only requires the
$\beta$-combination of the ordinary and $G$ folds to vanish, so (F) is
sufficient for view equality and not necessary.

**Step 4** (Lean: P27; `all_beta_joint_g_correction`, node P29). Both repair
families are fold-free: the R941 combination $x$ and the R686 $G$ correction
$g$ each have zero first fold in their conclusions.

## 4. Checking each condition

### 4.1 Inactive balance (B): holds for every witness difference, on paper

**Step 5** (source fact; refinement not proved). In
`crates/aspis-prover/src/state_only_hiding.rs`, after masks are added,
`balance_m31_copy_inactive` overwrites one relation-free cell on an inactive
row of each semantic column with minus the sum of all other inactive-row
cells of that column, witness cells included (lines 169–182, 710–716). The
mask-only columns, $G$ and the $H_1$ padding are balanced the same way (lines
453–470). So every honestly committed column has copy-inactive sum 0. R84 states
that the R102 host retains this operation.

**Step 6** (NEW ARGUMENT, immediate). For two executions with any witnesses and
any coins, each column difference has inactive sum 0, hence so does every
$K$-linear batch. By Step 1, (B) holds for the ordinary residual of every
pair, for D1–D5 alike. No determinant or probability enters.

This matters for D2 and D3: witness cells do sit on copy-inactive rows (the
Poseidon state rows are inactive but relation-used; e.g. value bits at rows
1009 and 1013 of column 3), so the witness difference alone is not balanced.
The balancing cell absorbs it.

Status: **paper**, conditional on the source fact of Step 5 for the R102 host
(inside the deferred refinement node P02). Node P17.

### 4.2 Exact image (I): equivalent to C1 coverage, which is unproved

**Step 7** (Lean: `natural_four_slot_coverage`, node P22). For any $n$
distinct fold coordinates the first $n$ natural coefficients of each slot
channel reach all $4n$ raw values. With the 89 pad coordinates of each semantic
column this covers the 88 raw openings of any 22-query schedule.

**Step 8** (count; source inventory). Each semantic column has 221–223 free
mask cells (3,803 relation-free cells over 16 columns). The view fixes, per
column, 88 raw values in $\mathbb F_p$, three point claims and two OOD values
in $K$: $88+12+8=108$ equations over $\mathbb F_p$. This is the "108-row,
rank 108" system of R84, R102, R538 and R546.

**Step 9**. By Step 2, (I) holds for the C1-corrected residual exactly when
each column's correction solves its two OOD rows. Full row rank 108 at a prefix
gives this for every witness difference at that prefix, because the matrix
does not depend on the witness. Rank 108 has been measured at two actual
prefixes and some synthetic ones. No theorem states it for all prefixes: Step
7 covers 88 of the 108 rows.

Status: **open** (node P14, then P16). Evidence: finite, two real prefixes.

### 4.3 First fold (F): not derivable from anything in the tree

**Step 10** (NEW ARGUMENT). The unknowns of the C1 correction are mask cells
in $\mathbb F_p$. For the batched quotient $Q=\sum_l\gamma^l q_l$, (F) is, for
each of the 256 blocks $d$, one equation over $K$, i.e. four over
$\mathbb F_p$, linear in those unknowns. The 22 query conditions already force
the fold polynomial to vanish at 22 points, so (F) adds at most
$4\cdot(256-22)=936$ further $\mathbb F_p$-equations, coupling all 16 columns
through $\gamma$ and $\alpha$. A single column cannot be fold-free on its own:
that would need about $88+936+20$ equations against 221 unknowns.

**Step 11** (count). Unknowns: about 3,787 free mask cells. Equations: $16\cdot
108=1728$ (Step 8), 4 for the initial mask claim (R538), 936 for (F): 2,668.
The system is underdetermined by about 1,119, so (F) is not excluded by
dimension. Nothing more is known: there is no rank statement, no determinant
polynomial and no numerical run for this system.

**Step 12** (why this is forced in the Lean route). By Step 4 the $H_1$ and
$G$ repairs have zero first fold. Final256 is public. Therefore the whole
ordinary-channel difference handed to R941 must already be fold-free, and the
only step before R941 is the C1 correction. In the Lean route the C1
correction must satisfy the 936 equations of Step 10.

**Step 13** (the validated route is a different construction). The numerical
diagnostics do not do this. Their $H_1$ system has 562 rows (568 with the six
ordinary relation rows of R28): 214 active, 88 raw, 3 points, 2 OOD and the
Final256 rows, rank 540 (545). There $H_1$ absorbs the fold left by an
arbitrary C1 solution. That $H_1$ correction is not fold-free, so it is not in
the 223-direction family of R941, and R941 says nothing about it. Conversely,
no diagnostic has built a fold-free C1 correction.

Status: **open** (node P15). The R893 and R941 notes name this themselves:
"Derive the fold, exact image and inactive-balance conditions for every legal
native same-public witness difference and its residual construction."

### 4.4 Per degree of freedom

| | (B) | (I) | (F) |
|---|---|---|---|
| D1 | holds (Step 6; both changed rows are active, so also trivially) | holds at the two tested prefixes; open in general | open; never constructed |
| D2 | holds (Step 6; needs the balancing cell) | open; never tested | open; never tested |
| D3 | holds (Step 6) | open; never tested | open; never tested |
| D4, D5 (collision witnesses) | holds (Step 6) | open | open |

Because the C1 matrix is witness-independent (Step 9), a universal rank
statement would settle (I) for D1–D5 together. The same is true of (F). The
$G$ step is different: the 626-row $G$ system has rank 602 with 24
compatibility rows, and whether the target satisfies them depends on the
witness difference and on the $H_1$ choice (R538, R541, R545). That has been
checked for D1 only.

## 5. Diagnostics rerun

All local, optimized, offline; peak RSS under 0.6 GiB, zero swaps.

1. The command as given, `cargo test --offline -p aspis-prover --release
   diagnostic_same_public_duplicate_input_selection_pair`, does not compile:
   exit 101 after 57.2 s, in the unrelated integration test `r9_hash_trace`,
   which needs the `insecure-spend-fixture` feature. The diagnostic did not
   run.
2. Replacement: the same test with `--lib --features insecure-spend-fixture`,
   together with the in-tree `v8_q22_same_public_local_separator` and
   `r16_basis_repair` modules: exit 0, 22 passed, 8 ignored (they need R17/R18
   host logs), 25.8 s. The two separator tests pass, which means **the
   separator survives on the in-tree encoder**: these tests encode with $E(m)$,
   the pre-R16 map, and assert the leak ($\lambda$ annihilates every column-0
   mask direction and takes the value 490597912 on row 913). They are negative
   regressions on the old profile. They do not exercise R102.
3. `rust/q22_fixed_pair_separator.rs` is not included by any in-tree module.
   It was run in a scratch copy of the prover crate: passes, i.e. the
   row-1014 functional on fibres 1 and 2 also survives on $E(m)$.
4. R102 adaptation, in the same scratch copy (nothing under `crates/` was
   changed). The R102 prover source is not in the tree; the adaptation uses
   the in-tree circle encoder and mask-cell inventory with the two-swap order
   reconstructed from R84 and checked against the Lean definition (pivot
   fixed; first 89 images 14, 15, 30, 31, …, 718; each relation-free in all 16
   columns). Under $T$ a mask direction at row $r$ becomes the unit
   coefficient vector at $\pi^{-1}(r)$. Results:
   - Raw observation matrix (rows: opened positions; columns: legal mask
     directions) has full row rank in all 16 columns on seven schedules:
     fibres {4,6}; {1,2}; 0..21; 1..22; the retained
     $[4,6]\cup\{1000+7919i\}$; a pseudorandom distinct schedule; the top 22
     fibres. Rank 8 or 88 as required, already from the first 89 pads alone.
   - The two retained functionals no longer annihilate the mask image: 85 of
     221 (column 0) and 85 of 223 (column 3) directions pair to a nonzero
     value.

   So no raw-opening separator survives on these schedules. This is the
   finite shadow of Step 7. **It is evidence, not a proof**, and it concerns
   raw openings only: it says nothing about (F), about points, OOD, Final256,
   semantic rounds, or the joint view.
5. The joint C1/H1/G diagnostics for the R102 profile (R102, R105, R546) live
   in frozen source trees on the build host and were not rerun: they are
   unchanged, their receipts are in the tree, and they cover D1 only.

## 6. Bound on $\varepsilon_{\text{algebraic\_bad}}$

No bound can be stated. What exists:

- Four determinant certificates, each for a fixed legal 22-root tuple under a
  product-uniform law on the remaining challenge coordinates:
  $819/p^4$ (two-swap $G$ residual, `bad_fraction_le_explicit`, R122, node
  P30); $1355/m$ (normalised $G$ core, R588, node P31); $1070/p^4$ ($H_1$
  active minor, R714, node P26); $14049/m$ (complete 223, R885, node P28).
  With $m=p^4$ their sum is $17293/p^4\approx 2^{-109.9}$.
- R122's adaptive first-read law (`lazyMean_eq_independentMean`, node P45),
  which would transfer such a bound to the real transcript if the honest
  challenge addresses were shown unread (node P10). The query roots depend on
  earlier challenges, so the fixed-root bounds do not apply as they stand
  (node P13).

$2^{-109.9}$ is a lower-level component, valid only after P10 and P13, and it
bounds only the event that one of four specific determinants vanishes. It
omits: failure of C1 coverage (no certificate); failure of the fold system of
Step 10 (no certificate); the $G$ compatibility rows for witness differences
other than D1; and the case where all determinants are nonzero but no
view-preserving coupling exists (node P1A). Until those have certificates,
$\varepsilon_{\text{algebraic\_bad}}$ is UNASSIGNED.

## 7. Gaps

1. **A1 (fold).** No theorem, polynomial certificate or numerical run shows
   that the C1 correction can be chosen fold-free (936 extra
   $\mathbb F_p$-equations, Step 10). R941's premise (F) is unmet for every
   degree of freedom, D1 included.
2. **A2 (two constructions).** The construction validated numerically ($H_1$
   absorbs the fold) is not the one the Lean theorems repair. Either a
   fold-absorbing $H_1$ theorem is needed, or the diagnostics must be redone
   with a fold-free C1 step.
3. **A3 (C1 coverage).** Full row rank of the 108-row per-column system is
   proved for 88 rows (P22) and measured for 108 at two real prefixes. The
   point and OOD rows, and the four-equation initial-claim coupling across
   columns, have no universal statement.
4. **A4 (which vector is $r$).** The map from a witness pair and a prefix to
   the vector $r$ is not defined anywhere, in Lean or in prose. Section 4
   assumes $r$ is the C1-corrected ordinary difference; the active-row values
   $r$ must carry (the $H_1$ helper difference) and the relation targets are
   then prescribed separately, as in R891. This reading is an inference.
5. **A5 (untested degrees of freedom).** D2 and D3 have never been run through
   any diagnostic. The $G$ compatibility rows depend on the witness
   difference.
6. **A6 (G premises).** R686 needs all seven plain relation coefficients of
   its input to vanish, a zero structured moment and a zero finish-coin
   moment of the 271-coordinate semantic difference. None is derived for a
   native difference (node P19a).
7. **A7 (balance at source).** Step 5 is read from the in-tree prover, which
   is the pre-R16 host; the R102 host is not in the tree.
8. **A8 (law).** The determinant bounds are fixed-root and product-uniform;
   their transfer to the adaptive transcript is open (P10, P13).
9. **A9 (coupling).** Existence of corrections for each pair is not yet a
   simulator. The corrections must compose into a coin bijection defined from
   the view alone, and the semantic messages depend on the masks
   nonlinearly; only the 271 $G$ coins absorb that (node P1A).
10. **A10 (Step 2).** The equivalence of (I) with OOD preservation is a
    dimension count made here, not a Lean theorem.
