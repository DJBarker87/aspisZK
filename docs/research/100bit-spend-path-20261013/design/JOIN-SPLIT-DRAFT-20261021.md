# Execution join split — draft, 21 October 2026

Branch `codex/cx-join-split-draft-20261021`, base `3a01b2d6d`. This
additive packet depends on the **unmerged** oracle-port draft. It is not
approval of that port and must not be merged before the user's approval.
Only new `OraclePortJoinSplit*` Lean modules are authored. Session A's
S1/S3/S4/S5/S9/S10 candidates, the sibling `OraclePortRowAware*` modules,
existing Lean modules, M10 instrumentation and shipped sources are read-only.

## Stage 1: total replacement interface

`OraclePortJoinSplitCore` defines thirteen executable cone owners and a
separate S10 call-site coverage predicate. An invocation is indexed by its
owner **and declaration name** and has dependent argument/result types.
Those types must preserve every mutable pre/post-state component and ordinary
Rust rejection. `Calls` preserves nested/repeated calls, return-dependent
branches and explicit oracle reads. It imposes no fictional chronological
ordering S1 → S2 → … → Pool; the frozen callers determine that order.

The exact all-input obligation for every executable cone `c` is:

```lean
∀ site, site.owner = c → ∀ args, source site args = model site args
```

Both sides are complete `Program Bytes State (σ.Value site)` values.
`PerConeJoins` names all thirteen obligations. `interpret_eq` proves their
substitution through the whole ordered, branching caller. `S10Join` requires
every invocation in every continuation to occur in the supplied inventory.
It intentionally adds audit coverage, not an extra execution stage.

`executionJoin_of_cones` derives the **unchanged** `ExecutionJoin D rust`
from those joins, S10 coverage and the explicit composition/ordering join:

```lean
source_order : ∀ i, rust i = interpret source (tree i)
model_order : ∀ i, interpret model (tree i) = verifier D dV i
```

The tree, signatures, implementations and inventory are parameters, not
constructed frozen artifacts. These two identities remain substantive caller
obligations. In particular, `model_order` must account for the port's extra
checks, early returns, duplicate handling and oracle reads, not merely prove
the same accepted-input arithmetic predicate. No frozen `ExecutionJoin` is
claimed by this substitution theorem alone.

Stage 1 focused compile: `OraclePortJoinSplitCore`, attempt 1, exit 0,
4.289 seconds, 3,659,743,232-byte peak RSS, zero swaps. All three theorem
audits use standard axioms only. Exact source/import hashes, revision,
command, output and timing are under
`evidence/join-split-draft-20261021/`; `manifest.json` records every attempt.

## Concrete decision stages and certificate adapters

The next stages add the literal dV decision skeleton, local certificate
instantiations and the endpoint consumer. They do not change the ownership
or source/runtime boundary described above.

## Release boundary

`StoredCarrierBinding D rust P runtime` is independent of the execution split
and remains exactly as in C7. Total program equality alone does not establish
checked arithmetic safety: R22 additionally requires outer Aeneas success
and the operational P6 `Translation` (or the precise Kani harness domain).
Focused cached-object checks are not a coherent frozen release replay.
