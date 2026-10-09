# Actual V7-prefix type adapter and the missing Merkle suffix producer

Inspected base `d0e56c281ea545832cfaec97334139fcbff8a440`.
Draft `lean/FSV7PrefixBridge.lean` imports the actual
`AuthenticatedEarlyC1Prefix` and `FSAuthenticationSuffix` modules.
No build or remote job was launched by this agent, as requested. This source
must be compiled/repaired against the parent's exact historical-source overlay
before any theorem is reported checked.

## Exact minimal conversion

| Existing authentication type | FS type | Adapter |
|---|---|---|
| `Byte = Fin 256` | `UInt8` | `toFin` / `ofFin`, inverse lists |
| `RawHashInput = List Byte` | `List UInt8` | elementwise bijection, preserving every byte/order |
| `Digest208 = Fin 26 → Byte` | projected first26 full-answer bytes | existing `fixedOfListD` on the encoded26 bytes |
| `AnswerPrefix = List (RawHashInput × Digest208)` | chronological input/answer record list | pairwise conversion |
| `OrderedRawQueryLog = List RawHashInput` | full input-bearing event log | preserve chronological inputs, including duplicates |

The draft proves inverse byte-list maps, exact26-byte digest roundtrip via the
old `fixedBytes_fixedOfListD_of_length`, root byte preservation, and literal
leaf/node serialization identities. Tags and lengths inspected in
`V7MerkleQueryGrammar` and `v7_merkle208.rs`:

- C1: `0x10 || 0x71 || value403 || salt32`, 437 bytes.
- C2: `0x10 || 0xf1 || value186 || salt32`, 220 bytes.
- Parent: `0x11 || left26 || right26`, 53 bytes.

`chronological_old_prefixes` derives the exact old-type `c1Answers`,
`c2Answers`, `c1Included` and `c2Included` premises plus stronger take
equalities from the actual extended causal `continueRun`. It does not accept
those premises or a blanket callback-agreement hypothesis. It remains a draft
until the real import closure is checked.

The total view defaults only outside the final recorded cache. No equality to
an actual hash oracle at unqueried inputs is claimed. Collision alternatives
must remain tied to actual log membership; the full256 underlying log is not
replaced by a weaker adversary view.

## Exact missing producer for SameBodyAuthenticatedSlots

The adapter alone cannot invoke
`same_body_authenticated_slots_or_failure` without these remaining facts:

1. `SuccessfulMerkleRun oldView query body`: parser/root/frontier verification
   must actually execute on the same body and query schedule.
2. `callsIncluded`: the selected sorted C1/C2 leaf calls and the successful
   internal-node trace must be emitted by the actual later script into the
   final shared log. No caller-supplied trace membership will close this.
3. The body roots must be the converted roots produced at the two chronological
   cuts. The adapter exports `root208` but does not assume root equality.
4. Actual Rust-to-functional byte parsing, bounded integer/Vec behavior and
   the source/adversary causal program connection remain separate.

The original grammar's old `disclosedQueryPairs=16` is not transplanted onto
this q22 path: `SameBodyAuthenticatedSlots`, `MinimalMultiproofPaths.leafLog`
and `SelectedWireMerkleRun` explicitly use `Fin 22` queries.

## Why a chronological Merkle script is a real next task

`RustShapedMinimalMultiproof.runPass` is a pure functional verifier. On each
branch it recursively obtains the tail result before constructing the current
`parent view ...`, then **prepends** the current two calls to its emitted
trace. Its resulting trace matches the Rust loop's intended current-first
order, but simply replacing pure hash evaluations with effects in that
recursion would execute them tail-first.

This is not a falsifier of its pure result theorem. It is precisely why one
needs an independent chronological script with:

1. current C1 parent request;
2. current C2 parent request;
3. recursive remaining entries using those two returned full answers' first26
   bytes and the correctly consumed frontier state;
4. next level only after the whole current level.

It must retain guard/fuel/frontier exhaustion failures and both roots. Prove
its successful result equals the old pure verifier under the final coherent
recorded view, and prove its emitted inputs are the same successful trace.
The selected leaf stage similarly executes `sortedOrdinals` in actual order,
two calls per ordinal. Previously prepared digests must not be silently trusted
or generated outside the shared log.

An initial bounded sublemma can implement one ordered two-tree parent Script
and derive both its exact two-input trace and `parent oldView` result from the
returned oracle's coherence. Then lift through one pass and the finite18-level
loop. This yields the `callsIncluded` producer; repeatedly proving generic
prefix inclusion cannot substitute for it.

No theorem/axiom audit, source rebuild, kernel replay, or new probability result
is claimed by this draft. No existing files changed, no commits/push by agent.
