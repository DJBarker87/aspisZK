# Fiat–Shamir for a round-by-round sound protocol: statement and proof route

2026-10-06. Lead design note. This fixes the theorem to be formalised for
premise FS of `R0_SOUNDNESS.md` §7. It is protocol-generic; it is not
instantiated here for R0 or V7. Nothing below is proved.

## 1. Design decision

V7's compiler (`V7Tag73ExactFixedK16Closure`) is a bespoke same-tape
state-restoration argument whose four stage events were never bounded. It is
replaced, for R0 and for V7's future use, by the standard shape: a
round-by-round state function plus a union bound over first oracle reads.
The compiler loss is then $Q_{\rm tot}\cdot\varepsilon_{\max}$ plus an oracle
collision term, with no fork parameter and no per-protocol compiler proof.
Every protocol-specific fact enters through the per-round bad sets, which
for R0 are those of §5–§6 and for V7 are its existing ledger terms.

## 2. Model

All objects are finite, as in the existing memoised-oracle Lean model
(`AspisV8R19.OracleProgramOps`, `MemoizedProgramLaw`, `AdaptiveFirstReadLaw`).

- Oracle $H:\mathcal I\to\mathcal A$, a uniform table; $|\mathcal A|=2^{256}$.
- A prefix of round $i$ is $(x,m_1,c_1,\dots,m_i)$; a transcript is a prefix of
  round $r$ followed by $c_r$ and a final message.
- Address map $\mathrm{addr}$: prefixes $\to\mathcal I$ (the duplex state).
  Premise (INJ): two prefixes with equal addresses are equal unless a
  collision among oracle outputs occurred; the collision event has mass at
  most $\kappa(Q_{\rm tot})$. Lean: `CausalDuplexCollisionBound`,
  `UniformFrameCollision` (V8 tree) supply the counting.
- Sampler: challenge $c_i=\sigma_i(a_1,\dots,a_{k_i})$ of the answers at the
  $k_i$ addresses the round reads; the exact laws of the ordinary, nonzero,
  circle and q22 samplers on fresh answers are in the tree (R601, R609,
  R417, R945).
- Adversary $\mathcal P$: any program making at most $Q$ oracle queries, then
  outputting $\pi$. Verifier $V^H(x,\pi)$: a program making at most $q_V$
  queries, re-reading challenge addresses (cache hits).
  $Q_{\rm tot}=Q+q_V$ bounds the number of distinct first-read addresses.
- Extraction: committed words are the preimages present in the table when
  the address carrying their root is first read. A preimage appearing later
  is a collision event, inside $\kappa$.

## 3. Round-by-round soundness (hypothesis on the protocol)

A predicate $\mathrm{doomed}$ on (prefix, table-at-first-read) with:

- (D1) the empty prefix is doomed when the extractor finds no witness for $x$
  in the table;
- (D2) for every doomed prefix of round $i$, every message $m_{i+1}$ and every
  table $T$: the fraction of fresh answer tuples $(a_1,\dots,a_{k_{i+1}})$ for
  which $(x,\dots,m_{i+1},\sigma_{i+1}(a))$ is not doomed is at most
  $\varepsilon_{i+1}$;
- (D3) a doomed complete transcript is rejected by $V$.

For R0, (D2) is exactly the bad-set table of `R0_SOUNDNESS.md` §6, with the
sampler laws converting "uniform challenge" to "fresh answers"; the bad sets
are functions of the prefix and the extracted words only, which is what D2's
quantification over $T$ requires.

## 4. Theorem

$$\Pr_H\big[V^H(x,\mathcal P^H)=1\ \wedge\ \text{extractor fails}\big]\ \le\
Q_{\rm tot}\cdot\max_i\varepsilon_i\ +\ \kappa(Q_{\rm tot}).$$

Knowledge soundness follows with the extractor of §2; plain soundness is the
case where "extractor fails" is "no witness exists".

## 5. Proof route

**Lemma A (first-read union bound; the one new generic lemma).** For a
memoised program with at most $N$ distinct first reads, and any family of
bad sets $B(a,T)\subseteq\mathcal A^{k}$ indexed by address and current
table, each of density at most $\varepsilon$: the probability that some
first read's fresh answer tuple lies in $B(a,T)$ is at most $N\varepsilon$.
Proof: `lazyMean_eq_independentMean` gives the fresh-answer law at each first
read with adaptive addresses and stopping; induct on the program, charging
$\varepsilon$ per first read. R931's `adaptive_success_domination` is the
closest existing shape and may be reused.

**Lemma B (deterministic inclusion).** Outside the collision event, if
$V$ accepts and the empty prefix is doomed, then there is a round $i$ at
which the transcript's prefix of round $i$ is doomed and its prefix of round
$i+1$ is not, and the fresh answers at $\mathrm{addr}$ of that prefix lie in
the bad set of (D2). Proof: by (D1) the root is doomed, by (D3) the complete
transcript is not; take the first round where doomedness flips. By (INJ) the
address of that prefix was first read exactly once and decodes to that
prefix, so the table at that read contains the extracted words the bad set
refers to.

**Composition.** Lemma B puts the target event inside (collision) $\cup$
(Lemma A's event with $B$ = the D2 bad sets). Lemma A with $N=Q_{\rm tot}$ and
$\varepsilon=\max_i\varepsilon_i$, plus (INJ), gives §4.

## 6. What the formaliser decides and what they do not

They decide the Lean representation of prefixes, the address map interface
and the induction in Lemma A. They do not change: the statement of §4, the
hypotheses (D1)–(D3), (INJ), the meaning of $Q_{\rm tot}$, or the treatment
of samplers as functions of fresh answers. If (D2) cannot be stated with the
table quantification above, or if Lemma B needs an assumption not listed,
that is a finding to report, not a premise to add.

## 7. Known limits

- $\kappa$ is a genuine term: for a 208-bit digest projection it is about
  $Q_{\rm tot}^2/2^{209}$; for the 256-bit duplex state about
  $Q_{\rm tot}^2/2^{257}$. Both must be carried, not dropped.
- $\max_i\varepsilon_i$, not the sum, is what the union bound charges; §6 of
  `R0_SOUNDNESS.md` reports both.
- This theorem is about the IOP-level transcript. The correspondence between
  R0 as written and any Rust verifier is the deferred refinement node and is
  not touched here.
