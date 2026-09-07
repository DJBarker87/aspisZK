# Decision at the investigated revisions: no-go for a certified V8

Latest: [joint-image-review.md](joint-image-review.md) proves the restricted
causal image/relation bound (118.4150 ideal bits) and confirms that installing
the gate requires a research-only verifier change. It adds no scalar values
to the 40,282-byte model. The full no-go remains: image-valid non-polynomial
adaptive recovery, source integration, full-view ZK and matched CU are open.

Latest: [adaptive-tail-review.md](adaptive-tail-review.md) rejects a query-only
recovery shortcut using a pre-OOD full-degree oracle, while leaving actual
accepted image/relation and adaptive outside probabilities unresolved. The
generic query-last identity survives; no complete security claim is upgraded.

Latest review: [lean-repair-review.md](lean-repair-review.md) kernel-checks the
generic fixed-target joint-query bound and root-product instance. The actual
adaptive accepted-provider-none obligation remains open. Current primary is
QM31 q22; the better-margin field-port fallback control is quintic q22 at
42,984 bytes, with quintic q21 retained as a thinner 41,692-byte control.
No complete security, ZK or CU-parity claim has been upgraded.

Subsequent review: [coverage-review.md](coverage-review.md) adds the q23
bounded-family control, quintic q22 margin comparison, a proved relaxed
joint-family theorem and newer isolated SBF evidence. The no-go on a complete
100-bit/CU-parity claim remains; historical frame failures below are superseded
for the tested kernels, not for a complete V8 entrypoint.

2026-09-07. Own source base `6f7edda9d9f64dee2fc7e7f852c85ac350c237ac`;
the experiments accompanying this document are additional research-only source.
Separate V8 branch audited through `ec74d86f114b53715fa3691aac87763fe72e4e26`.
The user's accepted 40,282-byte allowance is honoured. This is a research
decision, not an edit to the selected protocol or a declaration of impossibility.

**Do not call the current q22 design a demonstrated 100-bit, CU-parity V8.**
The fixed-family scalar theorem is valid, but does not establish the recovery
premise needed to apply it. The stronger full-fibre counterexample below rules
out assigning its 2,800-root budget to unconditional recovery even after both
agreement gates. The current partial provider filters out that failure; it
does not bound its probability. A complete V8 verifier/prover and matched
four-shape CU result also do not exist at the audited revisions.

This conclusion is firm about the proposed certificate and present evidence.
It is **not** a proof that q22 cannot achieve 100 bits with a different argument.
In particular, the new recovery lower bound is 101.246 bits, not a sub-100-bit
forgery. Neither this number nor the earlier isolated 99.246-bit example may be
relabeled as full-protocol attack security.

## 1. New falsifier: merely joining gamma and fold is insufficient for 104 bits

This is materially different from the earlier isolated-symbol experiment:
all four symbols in each fibre now have the same 29 component values, and the
construction passes **both** strict agreement thresholds for every fold alpha.

Let T=262144 fibres, J=9557 common fibres, and K=QM31. On the common fibres,
set every component to zero. On each remaining fibre s, use the coefficients of

    R_s(X) = product_{j=1..28} (X - (28*s+j)),  0 <= s < T-J.

Place coefficients 0..25 in the base-field C1 columns and coefficients 26..28
in H/G/D by base-field embedding. Copy them at all four fibre positions. This
is canonical malicious-oracle data of the actual widths. D is zero on the
common fibres and one everywhere else. The root intervals are disjoint, and
their maximum 7,072,436 is below p, so all roots are legal nonzero gammas.
The committed data is fixed before the OOD points and gamma; it uses no work.

Claim both 29-component OOD vectors are zero. For each of the 7,072,436 roots,
the combined zero codeword agrees on exactly 9558 complete fibres, or 38232
symbols: strictly more than 9557 and 38229 respectively. The virtual chord
quotient is zero on all these fibres, and its normalized four-point fold is
zero there for every alpha. Zero is a legal final256 candidate and satisfies
the two sparse chord-image constraints.

No same-support component tuple exists. Its D polynomial would have to vanish
on the 38228 common symbols, hence be identically zero by the actual circle
space's degree-1024 Laurent-numerator root bound. It would then disagree with
D=1 on the extra fibre. This argument does not assume a decoding conjecture.
It rejects full-support recovery, not every possible weaker extractor.

Consequently the joint threshold/same-support-recovery event has probability
at least

    7,072,436 / (p^4-1) = 252587 / 759558853319449026321387866774568960
                       = approximately 2^-101.2462242116.

This is greater than the proposed 2800/(p^4-1) budget by a factor 2525.87,
and greater than 2^-104. It does not contradict the new theorem, whose
`candidateMember` hypothesis explicitly assumes membership in the fixed tuple
family. It falsifies extending that theorem to missing-family branches.

Keep the queries separate: at one of these gammas the all-zero-fibre q22
subevent has 105.138775 bits; the joint rare-gamma/all-zero-fibre subevent has
206.384999 bits. Averaging this subevent over all gammas gives 105.142100 bits.
Other folded cancellations are not enumerated, and semantic, relation,
authentication and FS checks are not satisfied by this calculation. **There is
no constructed accepted payment proof.**

## 2. Positive result: the exact fixed-target query-aware lemma

Fix the 29 target polynomials, the received oracles, and legal OOD prefix
before gamma and alpha. Require that the target's OOD values match the prefix.
Let J be the number of fibres where every received component agrees with its
target at all four positions. Sample gamma, alpha independently and uniformly
from K\{0}, then a direct uniform q-subset of the T fibres. No prover selection
or FS resource lift is assumed by this lemma.

For a schedule containing a mismatching fibre, select one such fibre by a
fixed rule. One of its pointwise gamma residuals is a nonzero degree-at-most-28
polynomial. Therefore at most 28 gammas make all four residuals zero. For every
other gamma, invertibility of the normalized circle fold makes the residual a
nonzero degree-at-most-three polynomial in alpha. Chord denominators are fixed
and nonzero; they do not change these degrees. This proves

    e_fold = 28/(|K|-1) + (1-28/(|K|-1))*3/(|K|-1)
    Pr[all sampled folded residuals zero]
        <= b + (1-b)*e_fold,
    b = choose(J,q)/choose(T,q).

For J=9557, q22 this upper bound is about 2^-105.1420054893. Probabilities are
summed before taking logarithms. The scalar-only counterpart uses 28/(|K|-1).
No union over T locations is needed because the selected schedule is independent
of both challenges and the target was fixed beforehand.

This is a mathematical fixed-target lemma, **not the missing adaptive theorem**.
A malicious final polynomial may depend on gamma and alpha. One cannot first
fix it after seeing those challenges and then apply this argument. Likewise,
unioning 100 possible targets can lose log2(100)=6.643856 bits if no uniqueness
argument actually restricts the accepted target. The two-point fingerprint
proves uniqueness of an existing family member, not its existence or coverage.

The decisive next security experiment is now precisely stated: construct a
query-aware extraction partition covering the discarded provider branches,
with a pre-challenge target or an explicitly charged adaptive-family argument.
It must handle this full-fibre boundary and the earlier 760-gamma construction.
Do not substitute a gamma/fold-only 2800-root bound, or take a union bound over
100 targets while retaining the single-target 105-bit figure.

## 3. A checked published theorem does not supply the missing constant

DEEP-FRI, ITCS 2020, Theorems 3/25 and general-linear-code Lemma 28 use a
threshold containing `max(2L*(rho+epsilon)^(1/3), 4/(epsilon^2*|K|))`, with
the appropriate degree/distance term rho. If t bounds that expression,
eliminating epsilon gives `t^7 >= 256*L^6/|K|`. Even granting L=1 and dropping
rho, the formula can certify at most `(log2(|K|)-8)/7 < 16.572` bits here.
This is a limit of **that theorem's formula**, not an attack. The line-based
statement also is not a direct degree-28 curve theorem. Two OOD points do not
justify deleting its epsilon terms. A sharper theorem or new argument is
necessary. [Primary paper, §§3 and C.2](https://drops.dagstuhl.de/storage/00lipics/lipics-vol151-itcs2020/LIPIcs.ITCS.2020.5/LIPIcs.ITCS.2020.5.pdf).

## 4. Current decision frontier

| Route | Exact model body | Size decision | Security decision | Full-transaction CU |
|---|---:|---|---|---|
| QM31 two-OOD q22 canonical | 40282 | Accepted allowance; +282 over 40000 | Proposed recovery shortcut rejected; adaptive query-aware proof and ZK unresolved | Unmeasured |
| QM31 q21 canonical | 39037 | Fits 40000 | Same recovery gap; less query margin | Unmeasured |
| QM31 q22 packed fixed | 39934 | Fits 40000 | Same gap; packing may reverse V7's CU saving | Unmeasured |
| Full quintic q21 canonical | 41692 | +1410 over accepted allowance; +732 over 40 KiB | Known-stage field-port subtotal 100.326664 bits, conditional; not a full certificate | Unmeasured |
| Full quintic q21 packed fixed | 41292 | +1010 over accepted allowance; +332 over 40 KiB | Same theorem-port obligations | Unmeasured |
| Selective octic 16x q16 cap272 | 39980 | Nominal fit, 20 B to 40000 / 302 B to accepted allowance | Descent, actual list bound, wide hiding, enforced sampler unresolved | Unmeasured |

Quintic subtotal explicitly retains **two** old gamma terms, the old fold
term, 396430 and the named small algebraic terms, then adds the q21 query
probability. It excludes unproved field/source ports, FS and primitive terms;
passing that arithmetic is not a release certificate. Its larger field has
been independently certified, but that does not make the port automatic.

**Primary research direction:** QM31 q22 with query-aware recovery, retaining
canonical fields and the structured relation contractions. It has the smallest
architectural change and fits the accepted wire budget. Stop treating it as a
parameter-tuning task: the remaining security step is genuinely new mathematics.
Reject a purported proof if it assumes candidate membership, drops a provider's
discarded measure, or treats a post-challenge target as fixed.

**Fallback control:** full quintic q21, rather than the earlier octic priority.
It tests retaining the existing correlated-agreement argument without a subfield
descent theorem and without a 16x domain. This is a deliberate ranking change
after the recovery audit. It needs at least 1410 more canonical body bytes than
the accepted allowance, or a fully accounted saving of that amount. Its 164-MiB
dense-array model avoids the octic model's 2688-MiB dense arrays. Stop the fallback
under the present size constraint unless those bytes are recovered legitimately;
host product counts do not waive the full-CU requirement. Selective octic remains
a size-fitting exploratory option, not the better-supported fallback theorem.

No numerical CU relaxation has been justified. The +198 internal hashes and
+12 leaf hashes for q22 remain real work. The fast product and grouped-mask
contractions eliminate a feared dense new calculation, not this additional
authentication cost. A 2–5-second prover search cannot supply the missing proof.

## 5. Reused source/runtime/hiding evidence, accurately scoped

At audited `ec74d86f`, `V8A100ScalarFingerprintGammaBound.lean` and the ledger
prove fixed-family cardinality and conditional arithmetic. The scheduler-native
partial K14 provider still returns `none` on K13/K14 classifier errors. The
ledger SHA256 is `239fcb2d84cc61fa6adb1312263353cd87ca5bcf5fc8baf3603400dfdffb3d59`;
provider SHA256 is `c6652d78c19c6964bbfc0dcc3b7f56bd6f397ea4fdfe1d1e85466bacde44c381`.
These are committed snapshots; concurrent dirty files were not certified or edited.

The other branch's `results/v8-a100-q22/hiding-per-c1-source-gap-20260907.json`
records positive containment of all 1022 physical directions per C1 column
at one explicit legal Frobenius-conjugate schedule, including the forest layout.
This is stronger evidence than the earlier ambient-rank failure, which was
not a privacy break. It still is not universal full-view adaptive ZK, and the
source-connected linear maps required for that theorem are not translated.

Reused Linux evidence at `e8627859`, in
`results/v8-a100-q22/sbf-linux-baseline-20260907.md`, reports matched V7 withdrawal
CU 1153267 / 1218981 with verifier ELF hash
`3247628ca57225e5ca297b549c3aba0db6971c2480710751d1b25d600dfba204`.
Only two shapes were measured there. Do not splice them into the historical
four-shape table as if the binaries were identical. The same build diagnosed
unreachable V8 reference/optimized frames of 11904/18880 bytes, beyond SBF's
4096-byte frame limit. Those functions are absent from the V7 ELF. This is a
V8 implementation gate, not a V8 CU measurement or evidence of unsafe V7.

No remote job, deployment or large rebuild was launched by this continuation.
The source evidence is reused, not claimed as our execution.

## 6. Executed now

See [joint-results.json](joint-results.json) and `experiments/joint_recovery.*`.
The optimized Rust imports production QM31/M31, circle sampling and generator
constants. It checks 1914 mixed-width dots, 9240 literal normalized chord/fold
cases and 66 interval representatives including both endpoints. The universal
construction follows the explicit product and disjoint intervals; tests are
not probabilistic certification. Runtime: 0.34 s wall, 1556480-byte RSS, zero swaps.

Python independently exhausts a small boundary construction, 14739 fixed-target
root-set/query cases and 255 nonzero four-point affine-residual patterns over
F7. All verdicts are exact rational/integer comparisons; logs only display bits.
Final execution: 0.13 s wall, 17432576-byte RSS, zero swaps.

`lake env lean` checks the standalone `JointBoundaryArithmetic.lean`: eight
finite arithmetic theorems, each with empty axioms. Final exit 0, 3.91 s wall,
670023680-byte RSS, zero swaps. The first attempt unnecessarily evaluated 2^700
and failed the elaboration threshold; it was replaced with the small <2^124
field-size premise, not a larger resource limit. This is **not** a formal proof
of the whole counterexample, fixed-target lemma, protocol or simulator.

Reproduction commands from the research worktree root:

```sh
rustc --edition=2021 -O -C debug-assertions=yes docs/research/v8-no-work-100-20260907/experiments/joint_recovery.rs -o /tmp/aspis-v8-joint-recovery
/usr/bin/time -l /tmp/aspis-v8-joint-recovery
/usr/bin/time -l python3 docs/research/v8-no-work-100-20260907/experiments/joint_recovery.py
```

From the cached `/Users/dominic/ZK/AspisFormal` workspace:

```sh
/usr/bin/time -l lake env lean /Users/dominic/ZK/.worktrees/ZK-v8-no-work-100-20260907/docs/research/v8-no-work-100-20260907/experiments/JointBoundaryArithmetic.lean
```

The bounded research has therefore reached a **no-go decision for claiming or
selecting the current V8**, with a falsified reduction, verified useful arithmetic,
and an exact next mathematical obligation. Claiming either full feasibility or
general impossibility would go beyond the evidence.
