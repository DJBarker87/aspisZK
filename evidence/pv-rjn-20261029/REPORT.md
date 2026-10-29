# RJN — publication ordering and NodeAppend quantifier audit

Target not yet established. No complete ledger row or endpoint premise is removed. No
simultaneous-link satisfiability witness or decomposition credit is claimed.

## Boundary

Worktree `/Users/dominic/ZK/.worktrees/pv-rjn`, branch
`codex/pv-rjn-20261029`, base
`c8fb38ee734a84e8cdb4a3f8b8de697fd66195e7`.
Only new `PV_RJN_` Lean modules, own tools and own evidence are written.
`PV_RunJoin_` sources, all historical Link definitions, the live runjoin
branch/worktree, frozen Rust/client and the held RJQ branch/worktree are
unchanged. Other-branch reads use `git show`. No push or key operation.

## PublishOrder

`R1Z.PV_RJN_PublishOrder.actual` is checked with the **exact** unchanged
`PublishContext57.PV_RunJoin_Link_PublishOrder runs` conclusion.
`PV_RJN_NativePublishOrder.actual` specializes it directly to
`NativeCallback55.runOf data plans`, quantified over the still-independent
Data and Plan families. No particular actual-run family is invented.

Its explicit standalone producer Props state:

- `PV_RJN_Producer_Layout`: the Plan header is the actual MAGIC plus the S2
  tag and seven zeros, and its opening offset, node offset and total proof
  size equal the constants read by the source serializer.
- `PV_RJN_Producer_FrontRoom`: header length plus compact semantic length
  plus compact claim length fits `Usize.max`.

Neither producer contains an append law, model assembly, complete proof-byte
equality or the target link. They are source input/layout facts. They remain
obligations of the actual-family producer.

The proof obtains the source's successful codec calls, all ordered front
appends, the two commitment extractions, query append, node append and all
three length guards through `PV_RJN_PublishTrace.source`. It does not assume
an external `map_err` implementation: raw codec Results are retained in the
trace and their success comes from Fields under the producer size bounds.
`PV_RJN_Bytes.append_success` identifies each successful native byte append.
The existing query/node links then supply their local model transport, and
the proof establishes both model assembly guards and all final bytes.

The exact original PublishOrder link itself takes QueryAppend and the
**unchanged** NodeAppend as premises. It is a checked local conditional
serializer theorem, not a successful-run decomposition or endpoint discharge.

## NodeAppend obstruction and explicit correction

The checked rejection cells are `PV_RJN_NodeReject.body`, `.check`, `.count`,
`.tree`, `.first_slot` and `.source`. The sorted/deduplicated first batch of
an all-262144 array is the singleton `[262144]`. The proof uses a named
sorted-replicate lemma, a tiny ten-element dedup cell and isolated failure
cells; it never reduces the full multiproof or a concrete tree.

The conjunction under audit is problematic because `Fields r p` constrains
only the front fields. Substituting the 22 queries preserves Fields and all
commitments/tree. The actual tree check rejects 262144 because the strict
bound is 262144. Rejection occurs before the index-copy or tree-walk mutation
cone. `source-finding.json` records the frozen Rust hashes and the matching
failure-prefix inspection; this is not a new native association proof.

The selected-dictionary helper laws and `PV_RJN_NodeObstruction.no_successful_witness`
are checked. The native-family corollary is undergoing focused validation.
Their precise claim is that a successful,
front-associated publication plus the actual node offset is incompatible
with the **unchanged** NodeAppend link: that link equates both the successful
node result and the substituted rejection with the SAME model slot list.
The contradiction uses the link's own publication_indices law; it assumes
neither the substituted source rejection nor a desired serializer equality.

The explicit private correction candidate is `PV_RJN_NodeContext`:

Before:

```lean
∀ i p, Fields (runs i) p →
  slots.length=6 ∧ publication_indices_law ∧ node_append_law
```

After:

```lean
∀ i p, Fields (runs i) p → QueryRange p.queries → QueryContext (runs i) p →
  slots.length=6 ∧ publication_indices_law ∧ node_append_law
```

Every original conjunct and byte/error requirement is retained verbatim.
`PublishSkeleton57.PV_RunJoin_Link_QueryRange` and
`PublishContext57.PV_RunJoin_Link_QueryContext` already carry the separate
actual-run obligations. Range excludes this counterexample. Provenance
restricts the unrelated-publication quantifier just as for QueryAppend.
No sufficiency or satisfiability claim is made for this candidate. Existing
`PV_RunJoin_` definitions are read-only; the correction is not installed into
the live skeleton. This is a malformed-publication link counterexample, not a privacy
counterexample or a failure attributed to an honest native producer.
The six actual multiproofs and generic publication-index
source proof remain work for the corrected link, rather than a hidden new
producer hypothesis.

## Endpoint accounting

Whole rows removed: none. Endpoint P removed/added/weakened/changed:
**0/0/0/0**. No TrustItems field is added. The eight endpoint fields,
V370/D381/D386 compiler boundary, observer/simulator, coupling, failure
independence and side-channel obligations remain. QueryRange remains available from
the held RJQ result; no new QueryRange discharge is claimed. The actual-family and
simultaneous-link fixture witness remain runjoin58's work.
