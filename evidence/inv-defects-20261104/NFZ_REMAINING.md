# NFZ remaining obligations

**The requested compiler-backed repair is not complete.** No authoritative row
was dropped or promoted. This report does not license L187 final replay.

| Member | Done | Exact outstanding obligation and why it cannot be closed here |
|---|---|---|
| TX2:046 identity | Frozen type/trait definitions and source callers enumerated; body hash retained | Deployed MIR must show exact called impls and TX2 entry reachability, including whether optimized no-op tracing erases calls. Source aliases alone are not the required authority. |
| TX2:046 embedding children | M31/CM31/QM31 trait impls explicitly reported as absent-row candidates | Resolve reachability and transitive callees; add explicit TX1/TX2 occurrences for reached new functions. Do not quietly make the inventory stay at 587. |
| TX2:046 exclusion alternative | Row retained OPEN | If compiler evidence excludes it, retain the row with REACHABILITY-EXCLUDED and the evidence. No such exclusion is established. |
| TX2:211 | first_decoded callback and inactive legacy entry callback located | Deployed MIR must confirm the callback item and rejection edge; independent second MIR/symbol pass must agree. |
| Other callbacks | Whole-inventory AST scan and candidate existing-row flags retained | Resolve extension_limbs map edge, circle_fallback_point fallback closure and every unresolved candidate; recursively enumerate new nodes. Source closure ownership is not a compiler reachability proof. |
| Reviewed overlay | Empty SHA256-pinned overlay and additive producer exist | Admit only compiler-reviewed edges, through the producer; verify added domain obligations. Currently there are zero admitted edges. |
| Slice membership | Original NFQ closure re-derived: 585/587 | Recompute Q as well as D: hypothetical new edge from accumulate_batched_with_node expands Q by WideExact::from_m31. Original exact-Q assertion would fail; membership and caller obligations need review. |
| NFX count delta | All 587 statuses preserved exactly | Materialize repaired graph/new rows with OPEN obligations; reassess any newly discovered dependencies of CLOSED callers. Never infer new CLOSED status from membership. |
| Independent authority | AST/lexical discovery cross-check agrees | Neither is MIR or an ELF symbol pass. Required independent compiler/symbol authority remains absent. |
| Inherited graph delta | Exact two-occurrence to_le_bytes difference disclosed | Lead should identify historical downstream review provenance before asserting whole-graph re-derivation equality with raw NDT inventories; NFZ preserves NFX unchanged. |

## Budget and stop accounting

Kani 0/0, extraction 0/0, Lean 0/5; zero new Lean theorem or validator import
requires a compile. Every remaining semantic obligation above needs compiler
resolution or a reviewed inventory decision; using the five Lean slots would
not supply the missing MIR or validate an invented edge.

The explicit ONE capped scope is used (NFZ_B001). It was admitted and consumed
by my own overly strict metadata preflight, before the authorized scratch debug
build began. Exact refusal diagnosis and corrected own script are retained.
No further scope is launched. This respects the literal job limit rather than
silently treating an own-script failure as an additional authorized scope.
No timeout or memory-killed shape was repeated. There are no Kani-dependent
remaining obligations in this bookkeeping job; Kani remains prohibited.

Next concrete deliverable: under a newly allocated compiler scope, run the
corrected preflight and the frozen deployed-feature Cargo check with MIR and
typed-HIR diagnostics; validate all frozen source/lock pins before and after.
The existing NFZ_host.py deliberately refuses resubmission of NFZ_B001. A
follow-up must use a new attempt identifier and preserve these failed inputs.
Then review the candidate edges and explicit new rows, independently re-derive,
and regenerate the Q/S/D closures and status-preserving ledger delta.
