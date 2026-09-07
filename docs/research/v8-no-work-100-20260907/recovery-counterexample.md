# Conclusive rejection of the unconditional 28-gamma recovery shortcut

Date: 2026-09-07. Research source base f773b014e0fd03d4b1a1fd1c7060aa7bb14525f4.
The user-accepted body allowance remains 40,282 bytes. No production mutation.

## Decision, and its precise limits

**The leading q22 design's proposed unconditional replacement of the initial
coherence error by 28/(|QM31|-1) is false.** Exact counterexamples below use the
actual 26-base-column/three-extension-column gamma ordering and domain size.
The existing fixed-tuple Lean theorem is not false: its two tuples are fixed
before gamma, whereas these received oracles need not have a coherent tuple.

The sharper counterexample has an isolated initial same-support recovery error
of at least

    28,289,716 / ((2^31-1)^4 - 1), approximately 2^-99.24622563948648.

This is a **lower bound on that isolated stage's error**, unlike the previously
reported ~75-bit upper-bound certificate. Its exact comparison with 2^-100 is
also checked by a standalone Lean arithmetic certificate with no axioms.

It is **not** a complete accepted-payment attack, nor a lower bound on the
joint gamma/fold/query error. In particular the sharper example does not
automatically pass the next fold-agreement threshold. Therefore it does not
prove general impossibility of 100-bit V8, or even of a repaired two-point design.
It conclusively rejects a specific security reduction and any certificate
that sums this isolated recovery failure while assigning it 100+ bits.

## Source event being tested

`Pool/AlgorithmicCircleDecoderV7.lean` uses strict initial agreement >38229
and strict final agreement >9557. `Pool/V7CoherentTraceExtraction.lean` requires
`sharedSupport`: the selected combined candidate's entire agreement set must
be contained in the component tuple's joint agreement set. This is stronger
than merely identifying some nearby component tuple on a smaller set.

`state_only_spend_candidate.rs::gamma_combine_state_only_spend_codewords`
uses powers gamma^0,...,gamma^25 for the 26 M31 columns and gamma^26,...,gamma^28
for H,G,D in QM31. An arbitrary malicious committed oracle may contain any
canonical values with these widths. The adversarial columns below are all M31,
with the last three embedded in QM31; no illegal subfield assumption is used.

Both claimed component OOD vectors are zero. The zero combined codeword and
zero final polynomial are legitimate codewords. Given the false OOD values,
the virtual chord quotient is the received batch divided by the chord, so it
vanishes wherever the batch vanishes. Legal OOD points keep denominators nonzero
on the base domain. Merkle binding fixes these malicious leaves but does not
make their OOD claims true. No attack on the hash function is assumed.

## Construction 1: 760 gammas with complete-fibre agreement

Let M=760 and gamma_g=g+1 in M31, for 0<=g<M. For each four-point fibre f, put
the coefficients of the polynomial

    R_f(T) = product_{j=0..27} (T - gamma_((f+j) mod M))

in its 29 columns, identically at all four points. All polynomials are monic,
so D=1 everywhere. For gamma_g, the received combination is zero on between
9632 and 9660 complete fibres: >9557 fibres and >38229 original symbols.
The zero chord quotient and its zero fold agree on those fibres for every
alpha. This exceeds 28 bad gammas by a factor greater than 27.

Any component D codeword agreeing with the constant-one oracle on >38229
positions must be the constant one: a nonzero difference in the released
circle space has at most 1024 roots (via its degree-1024 Laurent numerator).
But constant one contradicts the claimed zero D value at either OOD point.
Thus these are genuine failures of prefix-compatible coherent recovery, not
merely two alternate descriptions of the same extracted tuple.

Exact Rust tests evaluate all 760*760 pattern/gamma combinations and reproduce
760 gamma dots with the actual mixed-width order. An independent Python count
uses pattern occurrence frequencies, not the Rust loop.

For perspective, the gamma-set probability is about 2^-114.4301. Given such
a gamma, the uniform q22 all-bad-fibre event has 104.8015–104.8937 bits.
Their joint probability therefore has about 219.23–219.32 bits. These are not
full acceptance probabilities; this example emphatically is not a sub-100-bit
forgery. Double counting gives at most floor(28*262144/9558)=767 gammas in this
particular fixed-zero, no-common-zero family, so the 760 construction is close
to its family maximum. That bound does not cover general adaptive candidates.

## Construction 2: the strict-threshold boundary

Now work at individual symbols, N=2^20. Choose a common set J of 38229
positions. Put all 29 column values equal to zero on J. For each remaining
position indexed s=0,...,N-|J|-1, put the coefficients of

    R_s(T) = product_{j=1..28} (T - (28*s+j))

in its columns. The root intervals are disjoint and their largest root is
28*(N-38229)=28,289,716 < p, so every root is a distinct legal nonzero gamma.

At each such gamma, the combined zero codeword agrees at exactly J plus one
additional position: 38230 symbols, satisfying the strict initial threshold.
If a component tuple agreed on that entire support, every component polynomial
would vanish at all 38229 common positions and hence be identically zero
(38229>1024). But the extra position has D=1. No same-support coherent tuple
exists. This argument needs no unproved list-decoding theorem or root scan.
The claimed zero OOD vectors match the zero tuple but do not repair its missing
joint agreement at the extra symbol. Uniqueness cannot manufacture that support.

This proves the stated 99.2462-bit isolated-stage lower bound. The verifier
cannot certify this stage with error <=2^-100 under the proposed unchanged
event definition merely by proving a sharper upper bound: the event actually
occurs more often in this experiment.

### Why this is not a full-protocol break

Choose J as the first 38229 symbol positions. It contains 9557 complete fibres
and one point of another fibre. The extra root occurs at only one additional
symbol. Thus complete zero fibres do not automatically reach 9558. Other
fold cancellations or an adaptive final candidate require their own analysis.
Charging gamma and fold failures jointly could be much smaller than charging
the isolated initial failure. An extraction definition allowing controlled
support loss could also evade this counterexample, but it changes the theorem,
agreement/list bounds and source bridge. Neither repair is implemented here.

## Executed evidence and limits

Commands from the research worktree root:

```sh
rustc --edition=2021 -O docs/research/v8-no-work-100-20260907/experiments/gamma_counterexample.rs -o /tmp/aspis-v8-gamma-counterexample
/usr/bin/time -l /tmp/aspis-v8-gamma-counterexample
python3 docs/research/v8-no-work-100-20260907/experiments/gamma_counterexample.py
```

Final Rust run: exit 0; 0.59 s wall; 0.05 s user; 1,753,088 bytes maximum RSS;
zero swaps and block input/output. Apple M3/macOS/Rust 1.93.0. No compilation
in the timed execution. 577600 polynomial evaluations, 760 mixed-width dots,
and 66 deterministic boundary instances. The full boundary construction is
proved by its product formula and disjoint intervals, not certified by sampling.
The program deliberately avoids expanding a million redundant polynomials.

`experiments/GammaBoundaryArithmetic.lean` checks only four exact numerical
claims (count, legal roots, >2^-100 comparison and fibre thresholds). It does
not formalize the complete field/code construction. Each `#print axioms` reports
no axioms. The standalone first check exited 0 in 0.62 s wall with 391,888,896
bytes maximum RSS and zero swaps. No Mathlib import, cold dependency build or
package replay was used. The cached repository `lake env lean` check is recorded
in the companion measurement artifact.

## Concurrent branch evidence: do not repeat or overstate it

The separate V8 branch advanced to e8627859856b792b2258d7e262b74d4199d5fc9d.
Its committed circle-DEEP bridge proves honest quotient representation in the
actual 1024-entry basis, including equal-x points. Reused evidence log reports
Lean exit 0, 6.47 s wall, 5,508,284,416 bytes RSS, zero swaps and standard
`propext`, `Classical.choice`, `Quot.sound` axioms. This run did not replay it.

An uncommitted `V8A100SchedulerNativeK14Provider.lean` was also inspected, SHA256
a419eed08d21c8835219622f4639ace5e0e6cfbc96f76228bbecd3cb9e7b8ae6.
It constructs a partial family by running the K1.4 classifier, returning `none`
on classifier failures. That is genuine source-interface progress, but does
not bound the measure of those discarded branches. The present counterexample
concerns that numerical recovery gap, not the legitimacy of partial providers.
All concurrent files were left untouched; no uncommitted proof was certified.

## Research recommendation after falsification

Retain canonical QM31 q22 only as a **design requiring a new joint recovery
argument**, not as the previously modeled 104.27-bit protocol. Its chord and
linear-link engineering now have concrete supporting evidence and its 40282-byte
layout is acceptable. The unrestricted 28-root recovery shortcut is rejected.
The smallest demonstrated repair is not a numeric byte/CU relaxation: it is a
different event composition or support-loss theorem. No honest search budget
can repair this logical issue. Selective p^8 remains the fallback, with its
previous field-descent, hiding, memory and CU obligations unchanged.

No investigated candidate is currently a demonstrated 100-bit, CU-nonregressing
implementation. The conclusive result of this continuation is the rejection
above, **not** a claim of general impossibility or a manufactured green result.
