# Partial-fold common-support recovery

Continuation from `d5507a8f247bbed7cd35591c240d8d7a40af67a0` on the existing
research branch. The initial worktree was clean. Production, main, verifier
grammar, q22/domain/field and the 40,282-byte cap are unchanged by these leaves.

**Evidence status:** both the generic and selected common-support, radius
and challenge-count endpoints are kernel checked. The independent geometry
control remains separately scoped. This advances partial-word recovery but
does not establish image validity, payment extraction, or a global bound.

## New recovery statement and its exact scope

Fix an arbitrary received virtual quotient `R` before `alpha0`. Let four
distinct alpha values have final256 messages, each allowed to depend on
its own alpha. Let `S` be any set of final-domain fibres on which all four
actual normalized folds match those respective final codewords.

The common-support theorem constructs a single full natural1024 quotient
coefficient vector `q` satisfying

```
exactInitialEncoder(q)[childIndex(i, slot)] = R[childIndex(i, slot)]
for every i in S and every slot in Fin 4.
```

This conclusion concerns **all four original symbols per fibre**, not just
the normalized folded value. There is no original-code/image membership,
anchor, provider success, or received polynomiality premise. The constructed
polynomial is in the full quotient space; its reconstruction image and
component-wise semantic meaning still require their own checks.

The proof restricts the actual final encoder to `S` and interpolates the
cubic-in-alpha fold there. Its four coefficient words have global message
preimages because they lie in the range of the restricted linear encoder.
Those messages are packed using the actual `slotIndex`/`parentIndex` order.
The existing `radix4Evaluate_radix4Decode` identity reconstructs every
received slot on `S`. Thus this is not merely a union-of-bad-sets argument.

Only after that algebraic construction, if every chosen final has at most
`B` bad final fibres, we choose `S` as the complement of their union. The
constructed full quotient has at most `4B` bad complete original fibres.

Contrapositive:

> If every full quotient codeword differs from `R` on more than `4B`
> complete fibres, at most three alpha values admit **any** final256
> codeword with at most `B` folded discrepancies.

This permits adaptive final selection directly through an existential
final at each alpha. It does not freeze that selected final before alpha.
The received word, domain, encoder and inverse tables are fixed across the
challenge experiment. They may depend on the legal earlier transcript.

## Numerical reach: useful recovery, weak query-only suppression

The conclusion does **not** provide the desired 100-bit accepted-recovery
bound. For the far premise to be nonvacuous, `4B < T`, where `T=262144`, is
necessary, not sufficient. Using only this necessary condition gives the
optimistic ceiling `B=65535`; selected-code covering constraints may reduce
it further. Outside the at-most-three exceptional alphas, the actual
chosen final has at least `B+1` discrepancies, so its matching count is at
most `196608`. Under genuinely fresh uniform distinct q22 queries the
largest allowed query-passing fraction is

```
choose(196608,22) / choose(262144,22) ≈ 2^-9.13124877642.
```

The root's exact parameter/control harness records that fraction; it is a
pointwise-query diagnostic, not scalar-batch or terminal acceptance.
A conservative conditional pointwise screen adds `3/k` to this query term,
or uses `3/k + (1-3/k)*query_term` under the corresponding disjoint alpha
partition. It does not approach 100 bits. No relation-repair event is
charged by this geometric theorem itself, and none should be counted twice
when it is eventually composed with the repaired relation game.

The new result rules out an unsupported recovery jump from four nearby
folded finals to a radius smaller than `4B` using only these hypotheses.
It does not rule out a stronger conclusion using the actual selected code,
image gate, point rows, batching structure, or more detailed agreement
information.

## Sharp generic control

The parent investigation's `experiments/partial_fold_control.py` uses seven
genuine nonzero F31 circle fibres with distinct final positions. Four
decoded coefficient tuples are the cubics

```
r_i(X) = product_{j != i} (X-a_j),    a = [1,2,3,4],
```

and three decoded tuples are zero. For the constant final code, at alpha
`a_i` only fibre `i` differs from zero, so each of the four finals is
1-close. The nearest full lifted constant-code word nevertheless differs
on four fibres: the zero decoded tuple has maximum multiplicity three,
and each of the other four tuples appears once. The actual four-slot map
is invertible at every selected circle point.

The control exhausts all 31 alpha values and 31 constant final messages
for this fixed word (961 pairs), and computes optimal pointwise q2
acceptance `47/217`. This is not a search over all commitments, complete
relation strategies or selected QM31 oracles. The example proves the
factor four is sharp for the generic constant-code hypotheses, not that
the selected image/row-aware design cannot do better.

## Existence versus executable extraction

The retained proof constructs code preimages by classical choice in the
restricted encoder range. It is not an implemented replay extractor.
Given the four final messages explicitly, a direct coefficient recipe is
available: for each lane `j`, take

```
message_j = sum_a coeff_j(LagrangeBasis_a) * final_message_a,
q[4*index + j] = message_j[index].
```

This is a finite field algorithm using only those four supplied message
vectors and distinct alphas. Its explicit equality to the chosen proof
object and an executable implementation are not claimed here. More
importantly, the verifier supplies only one sampled final per execution;
obtaining four legal fixed-prefix continuations and their required
agreement certificates is an additional extractor-access/resource problem.
No Merkle root is treated as full-oracle access, and no `none` outcome is
discarded.

## Theorem map and provenance

| Leaf / declaration | Intended implication |
|---|---|
| `PartialFoldRecovery.four_support_folds_recover` | Actual four-slot reconstruction on the four folds' common support |
| `PartialFoldRecovery.four_close_folds_recover` | Full lifted quotient within `4B` complete fibres |
| `PartialFoldRecovery.far_close_fold_challenges_le_three` | Distance greater than `4B` ⇒ at most three `B`-close challenges |
| `PartialFoldSelected.four_selected_support_folds_recover` | Same support conclusion for the actual stored log20 natural1024 evaluator |
| `PartialFoldSelected.four_selected_close_folds_recover` | Actual selected code radius bound |
| `PartialFoldSelected.far_selected_close_challenges_le_three` | Actual selected-code near-final challenge count |

The selected leaf consumes the previously checked `ExactFoldSelected`
encoder/lift identity and canonical inverse tables. It does not assume
the code identification merely because those files are imported. The
committed V7 mathematical encoder and fold map are connected explicitly;
the full Rust parser/virtual quotient/source transcript and resource-bounded
FS connection remain separate.

Borrowed Aspis sources are checked against immutable main
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; untracked main K13 files are not
imported. The runner uses the existing Lean 4.32.0 / Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997` cache, `-M7000`, and serialized
7-GiB aggregate child-RSS guard. No cold dependencies or unchanged complete
replays are scheduled.

| Log | Exit | Wall seconds | Peak RSS bytes | Swap | Meaning |
|---|---:|---:|---:|---:|---|
| `partial-fold-recovery-v1.log` | 1 | 21.49 | 5,487,132,672 | 0 | Reserved `matches` identifier; renamed before retry |
| `partial-fold-recovery-v2.log` | 1 | 15.29 | 5,459,918,848 | 0 | Support theorem passed; remaining `Nat` numeral cast in the union cardinality |
| `partial-fold-recovery-v3.log` | 0 | 24.24 | 5,575,868,416 | 0 | All three generic endpoints; standard axioms only |
| `partial-fold-selected-v1.log` | 1 | 15.30 | 5,592,612,864 | 0 | Actual support theorem passed; dimension metavariable at standalone distance headers needed `m := 262144` |
| `partial-fold-selected-v2.log` | 0 | 22.26 | 5,681,463,296 | 0 | All three actual selected-encoder endpoints; standard axioms only |

Generic source SHA-256:
`3a540b9f1fc205bd8dbbb9676413a45e983c564c27f6abb97bcb1fed0859c0e9`;
generic olean SHA-256:
`ac4e4bb059de77d954a24de343d9282ca22ea1a94bf2e5968a7f4344918d28ee`.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in the three
audits; there is no `sorry` or new axiom in retained claims. The generic
source is frozen after its successful replay.

Selected source SHA-256:
`77cce90fa4874c75a00426e0c02ec7944941e56fd6eb6751854d28364932099e`;
selected olean SHA-256:
`72f9ff53706cab6f6eedea5e80b559ceaf87fc877bb361f245b4799a338559dd`.
All three selected audits likewise contain only `propext`,
`Classical.choice`, and `Quot.sound`. The successful selected source is
frozen; the runner records and checks the imported generic/source oleans
and the 231-module committed Aspis closure before and after the replay.
The inherited exact-encoder source/olean hashes are pinned explicitly in
the runner and the log. No dependency closure was rebuilt and no unchanged
old theorem was replayed.

```
bash docs/research/v8-no-work-100-20260907/experiments/run_partial_fold_recovery.sh /absolute/NEW.log
bash docs/research/v8-no-work-100-20260907/experiments/run_partial_fold_recovery.sh /absolute/NEW-selected.log PartialFoldSelected
```

The accepted-extraction residual remains visible: image/ordinary-row
constraints, component recovery, early C1 causality, authenticated access,
semantic-to-checked-payment extraction, replay/fuel failures and FS resources
are not bounded by this lemma. The next decisive mathematics must use some
of that additional structure to control partial-agreement accepted mass;
another radius-only union bound cannot meet the contract.
