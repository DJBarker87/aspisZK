# Accepted execution refinement — unmerged draft, 21 October 2026

Branch `codex/cx-refine-join-draft-20261021`, based on inner-order draft
`d1ed5eed9`. The lead must not merge this packet before user approval of the
oracle port. Existing Lean modules, candidate re-pins, M10 and shipped source
are read-only. This packet uses new `OraclePortRefineJoin*` modules only.

## Accepted execution interface

`OraclePortRefineJoin.ExecutionRefinement D rust` is verbatim:

```lean
AcceptedRefinement rust (verifier D OraclePortShortCircuit.outerDecision)
```

`AcceptedRefinement source model` is verbatim:

```lean
∀ H i, (eval H (source i)).2 = true →
  (eval H (model i)).2 = true ∧
    (eval H (source i)).1.Subperm (eval H (model i)).1
```

`i : Input` preserves the public statement, proof function and stored bytes.
The oracle world is the same. `execution_join_refines` proves the inherited
`ExecutionJoin` implies this predicate; `outer_join_refines` covers the
outer-short-circuit join. `accepted_budget` gives 1161 queries on accepted
source runs; `accepted_no_extra` gives containment of each source read.
`rejected_read_refines`/`rejected_read_not_equal` witness strict weakening
for every model with a rejecting input. Nothing bounds rejected source runs.

## Consumer obstruction: containment is not extraction transport

The consumer's event is
`run.accepted ∧ RawRecordedPublicSpendExtractorBin.extract run coins = none`,
not acceptance alone. `runtime_transport` currently rewrites the whole
accepted annotated run. Its constructor `annotatedWith` records one execution,
uses `build D` to enrich the proof, then runs the verifier again.

`OraclePortRefineJoinRecoveryObstruction` compiles two countermodels:

* `sparse_refines_rich`: a source which accepts without reading refines a model
  which reads one leaf and accepts, for every input and oracle. The actual
  `RawCutRecordedWordsExecutableBin.recoverAtExec` returns `none` on the source
  log and `some ([],salt)` on the model log. The witness uses width zero and an
  empty path to isolate the same primitive used by the production extractor;
  it is not a valid full protocol proof.
* `cut_permutation_counterexample`: equal full read multisets can have different
  `cutBeforeExec` prefixes. Moving a leaf across a frame loses it from the cut.

These refute a generic recovery-preservation rule from the proposed
containment direction. They do **not** refute `dV_sc` soundness, the desired
full protocol theorem, or the frozen slot's accepted-run refinement. The
missing protocol-specific argument must show that the frozen execution has
all recovery-relevant reads before the same commitment cuts (and gives the
same annotation words), or change the runtime/extractor to replay the model
and prove its cost/observation contract. A query budget alone gives neither.
One must also account for the two passes of `annotatedWith`; arbitrary Rust
programs need not preserve acceptance under proof enrichment.

Consequently there is no claimed `OraclePortHeadlineRefine` with the requested
signature in this packet. No premise deletion is claimed. R19 and the existing
draft endpoints remain unchanged. The exact candidate signature replacement
and the failed transport step are recorded in evidence; this is an obstruction
to the proposed black-box proof, not a full-verifier counterexample.

## Independent frozen-slot results

`OraclePortRefineJoinSlot.padding_guard_erasure` proves that accepted
`slotTail` evaluation is exactly the same as `verifyInPlace` on the counted
prefix with that padding guard erased. This establishes that the guard can
only restrict acceptance, including on arbitrary raw `Parsed` inputs.
`accepted_leaf_log` proves by induction that a successful frozen leaf scan
queries every source position including duplicates, in the sorted source
order. `successful_levels` constructs the full successful level chain by
induction on height without evaluating height 18. `padding_witness_direction`
checks that the inherited nonzero-padding witness cannot refute the requested
one-direction implication.

These are source-side facts. The general theorem

```lean
(eval H (verifySlot_frozen p q batch kind)).2 = true →
  (eval H (OraclePortBatchDraft.verifySlot p q batch kind)).2 = true
```

and its accepted-read multiset consequence are still open. In particular,
source nodeCount/consumed siblings must be identified with orderedFrontier,
and the sorted live-prefix level invariant with the recursive selected tree.
The height-chain theorem is not that missing invariant. No additional raw
slot counterexample was found. This limitation is separate from the generic
consumer obstruction above; the latter does not make the slot claim false.

## Refinement-form join split

The existing join table remains a read-only historical equality interface.
This table supersedes its delivery *form* for this draft, without claiming
any frozen implementation inhabits an obligation. `R(c)` is verbatim:

```lean
∀ site, site.owner = c → ∀ args, ValueRefinement (source site args) (model site args)
```

`ValueRefinement source model` is verbatim:

```lean
∀ H, (eval H source).2 = (eval H model).2 ∧
  (eval H source).1.Subperm (eval H model).1
```

Unlike accepted-only Boolean refinement, this retains complete intermediate
results/state even on ordinary rejection. The caller can branch on them.
`cone_join_refines`, `bind_refines`, `interpret_refines`, and
`execution_refinement_of_cones` prove old equality implies the replacement
and that these replacements suffice for the new execution refinement.
`accepted_child_counterexample` demonstrates why accepted-only refinement
cannot be substituted in an arbitrary value-dependent caller. `short_refines`
proves it does suffice for the actual short-circuit Boolean-AND shape.

| Cone | Delivery form where sufficient | State/observations still required |
| --- | --- | --- |
| S1 | `R(.s1)` | Prepared, powers, semantic claims, scratch and complete return state |
| S2 | `R(.s2)` | Observer-off dispatch, byte slices, child errors and full state |
| S3 | `R(.s3)` | Group tables/masks, weight-loop values and state |
| S4 | `R(.s4)` | All four dots, limbs/batches, prefix reads and returned state |
| S5 | `R(.s5)` | Strict decode, tower/kernel values, errors and final state |
| S6 | `R(.s6)` | Public/proof/k, callbacks, complete checkpoint bytes and errors |
| S7 | `R(.s7)` | Selected values, geometry/readers, accumulator/Vec and full loop state |
| S8 | `R(.s8)` | Accumulator, residue/row traversal, finish result and caller writes |
| S9 | `R(.s9)` | Factored power/weight-loop values and complete state |
| S10 | Unchanged `S10Join inventory tree` | Declaration/source coverage of all continuations; not an executable cone |
| Parser/codec | `R(.parserCodec)` | Exact parsed Option/Err, offsets, canonical guards and reached fields |
| Multiproof | Accepted Boolean refinement at short-circuit slot boundary; `R(.multiproof)` at general value-returning calls | Successful roots, duplicate consistency, level/frontier correspondence, accepted read containment; the general source-slot theorem remains open |
| Checkpoint ABI | `R(.checkpointAbi)` for execution; equality/causal laws for observed ABI | Exact 1768-byte payload/state and same-input provenance; arbitrary read permutation does not establish runtime or recovery-cut compatibility |
| Pool caller | `R(.poolCaller)` for execution; preserve externally observed calls separately | CPI/account/public/proof/checkpoint/hint bytes, ordinary errors, same snapshot and transaction order |

These forms suffice for **execution refinement**, not by themselves for the
recorded extractor headline. Existing pin/backend/checked-arithmetic/totality
and caller obligations from `JOIN-SPLIT-DRAFT-20261021.md` all remain.
Accepted-only cone refinements also do not establish R22 totality on rejected
inputs. No re-pin file was edited.

## What probability transfers now

`OraclePortRefineJoinConsumer.acceptance_event_transport` proves the exact
lazy memoized-oracle inequality for any event depending only on acceptance
and the shared `Input`. `acceptance_failure_bound` specializes it to
`ExecutionRefinement D rust`. This confirms the one-direction argument for
acceptance-only bad-input events. The current `failureMass` is not such an
event. Its dependence on the log and reconstructed words is precisely the
remaining consumer issue; neither lemma silently substitutes a new event for
that headline's event.

## Exact recovery residual, not a new hidden source premise

`OraclePortRefineJoinExtractionTransport.RecoveredInputAgreement source model`
has exactly these fields:

```lean
decoded_public : runDecodedPublic source = runDecodedPublic model
initial : initialWordsFromRun source = initialWordsFromRun model
final : finalWordFromRun source = finalWordFromRun model
```

`extractor_eq_of_recovered_inputs` proves equality of the **unchanged actual**
extractor at every coin tape from these fields. Together with acceptance
inclusion, `failureMass_le_of_recovered_inputs` proves the exact pointwise
failure-mass inequality needed by `lazyMean_le_of_eval`. No probability or
failure-mass premise is used to prove that lemma. However, the fields are not
proved from `ExecutionRefinement`: deriving them for accepted two-pass source
annotations is the remaining protocol-specific task. They have not been
smuggled into a claimed headline replacement.

`OraclePortRefineJoinStrict.execution_refinement_strict` additionally proves
strict weakening at the actual inherited eager verifier. Starting with any
Input seed, it overwrites only the public tag with zero to exhibit a rejecting
input, and adds one read after each rejection. The new source satisfies
ExecutionRefinement but fails ExecutionJoin. This strengthens the earlier
conditional strictness construction to the concrete model without assuming
that a rejecting input exists.
