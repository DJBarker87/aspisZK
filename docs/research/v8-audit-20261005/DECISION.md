# V8 audit: decision memo

2026-10-05. Base `4e0f47381`. Profile
`AV8/R102/sparseG-bitperm-two-swaps/quadratic-channel-fold/merkle8-research-v1`.
"Closed" means a named Lean theorem in the tree, re-bound in `lean/V8Audit/`
with a clean axiom audit.

## 1. Verdicts

**Question A, privacy coverage: OPEN.** No stop condition. Of the three R941
conditions, inactive balance holds for every witness difference on paper: the
prover balances every committed column over the copy-inactive rows (one source
fact). Exact image is equivalent to the C1 correction preserving both OOD
vectors; that is proved for the 88 raw rows and measured (rank 108) at two real
prefixes. The fold condition is not derivable from anything in the tree. Both
Lean repair families (R941 for H1, R686 for G) are fold-free, so the C1 step
would have to satisfy up to 936 further base-field equations coupling all 16
columns, and no theorem or run addresses that system. The numerically
validated construction lets H1 absorb the fold, which is not the construction
the Lean theorems repair. Only the duplicate-slot witness difference has been
tested; leaf-position and lane differences have not. Diagnostics: the old
separators survive on the in-tree pre-repair encoder, as those tests assert;
under the R102 transport no raw-opening separator survives on seven schedules
in all 16 columns. That is evidence, not proof. `epsilon_algebraic_bad` has no
bound; the four determinant certificates sum to $17293/p^4\approx2^{-109.9}$
under a law that is not the transcript's.

**Question B, soundness without grinding: OPEN; stop condition triggered.**
The nine round targets sum to $2^{-104.26}$. The gamma and alpha0 targets are
root counts for a tuple family fixed before the challenge. No theorem supplies
that family for every accepting branch, and the 7 September full-fibre
construction ($2^{-101.25}$) still refutes the unconditional form. The theorems
that exist at these thresholds give 75.74 and 80.90 bits for those rounds. All
three open classes of 7 September remain open; the R19 channel fold adds
extraction of the quotient pair before beta. There is no Fiat–Shamir theorem
for the R102 transcript. No forgery is exhibited.

## 2. Numbers

| | closed | conditional | open | deferred |
|---|---:|---:|---:|---:|
| Privacy (52 nodes) | 25 | 6 | 21 | 0 |
| Soundness (26 nodes) | 6 | 4 | 16 | 0 |
| Refinement (2 nodes) | 0 | 0 | 0 | 2 |

- 2,128 Lean files, 275,441 lines; 1,344 files (63.2%) and 177,245 lines
  (64.3%) feed a closed or conditional node. 1,021 of those files are the
  closure of one node, the R885 determinant bound. 31 feed a soundness node.
- Orphans: 348 refinement-deferred, 199 generated chunks, 127 unused, 110
  superseded-design.
- No closed node mentions the R102 prover, verifier, transcript or view; the
  tree has no Lean model of them. All seven ledger terms are UNASSIGNED.

## 3. Critical path

Privacy, modulo the deferred refinement node P02:

1. P03 seed hop — oracle
2. P04 salt hop — oracle
3. P09 merkle8 commitment trace — oracle
4. P10 honest challenges first-read — oracle
5. P11 joint sampler law — probabilistic
6. P12 witness-independent aborts — probabilistic
7. P13 determinant bounds under the adaptive law — probabilistic
8. P14 universal C1 coverage — algebraic — **blocked by A** (gap A3)
9. P15 fold-free residual — algebraic — **blocked by A** (gaps A1, A2, A4)
10. P16 exact image — algebraic — **blocked by A** (follows from P14)
11. P17 inactive balance — algebraic — holds on paper; needs the source fact
12. P19a G-step premises — algebraic — **blocked by A** (gaps A5, A6)
13. P1A view-preserving coupling — composition — **blocked by A**
14. P1B retry and publication law — probabilistic
15. Compositions P05c, P06c, P07c, P18c, P19c, P08c, P01 — composition

Soundness, modulo S02:

1. S24 list caps rebound — algebraic
2. S20 pre-gamma tuple list — probabilistic — **blocked by B**
3. S11 OOD pair — probabilistic — **blocked by B** (needs S20)
4. S21 pre-beta quotient pair — probabilistic — **blocked by B**
5. S22 far-final accepted mass — probabilistic — **blocked by B**
6. S18 relation rounds — probabilistic — **blocked by B** (needs S21)
7. S23 payment-witness extraction — probabilistic
8. S10 semantic rounds — probabilistic
9. S03 Fiat–Shamir compilation — oracle
10. S04 arithmetic, then S12c, S13c, S15c, S01 — composition

## 4. Not fixed at this base; each is an input to source refinement

1. The ordinary residual construction: which vector plays $r$ in R941, and
   whether C1 is fold-free or H1 absorbs the fold (A1, A2, A4).
2. The protocol, if Question B requires a change to reach 100 bits.
3. The Lean model the source is refined to: experiment, view, game sequence,
   simulator interface. None exists.
4. The seven ledger terms as numbers, and the meaning of "100 bits": round
   errors below $2^{-100}$, or acceptance below $2^{-100}$ at a declared
   $(Q,R)$ envelope.
5. The R102 prover and verifier source in the tree. `crates/` holds the
   pre-R16 host; the sources of manifest `26755a42…` are on the build host.
6. The source invariants the paper arguments use, starting with the
   copy-inactive balance of every committed column.

## 5. What could not be done as specified

1. The `cargo test` command as given does not compile (exit 101; unrelated
   test `r9_hash_trace` needs a feature). Run with
   `--lib --features insecure-spend-fixture` instead.
2. The R102 prover source is not in the tree. The raw separators were adapted
   in a scratch copy with the in-tree encoder and the two-swap order; the
   joint C1/H1/G diagnostics on the build host were not rerun.
3. Lean ran on the build host (no compiled V8 cache here). Fifteen existing
   leaf modules absent from that cache were compiled unchanged into a separate
   directory to check the bindings. No new lemma was proved.
4. Open nodes about objects with no Lean model are named opaque propositions;
   their content is the docstring. Composition nodes are stated, not proved.
5. No ledger term received a numeric target; none is on record for a whole
   term.
6. The V7 list-cap and correlated-agreement theorems were not rebound.
7. Published bounds are cited from memory; no paper was re-fetched.
8. `CURRENT_STATUS.md` and `R16_SOUNDNESS_OBLIGATIONS.md` were read in part.
   Soundness work on other branches is not in this tree and was not audited.
9. Which vector plays $r$ in R941 is an inference; the tree does not say.
