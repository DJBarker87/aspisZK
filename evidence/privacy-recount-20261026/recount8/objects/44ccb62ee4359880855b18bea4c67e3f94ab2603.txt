# D277 bounded extraction stop

The concrete helper-closure route is stopped under the user's explicit
outside-`records` boundary. No source outside records was edited.

`pv15-records-charon-30` uses unchanged pinned Charon/driver/Aeneas binaries,
optimized MIR, the frozen records source, and **no opaque child functions**.
It exits 0 with four extraction warnings, but its LLBC has `has_errors=true`.
The required preflight rejects it before reservation or Aeneas execution
(`pv15-records-aeneas-30-preflight-rejection.json`). Exit 0 is not accepted as
successful extraction. No R_shipped definition is accepted or emitted.

The LLBC contains five `Opaque("ConstEvalVal")` constant occurrences:

| Function (all outside records) | Rust source span | Opaque occurrences |
|---|---|---:|
| `poseidon2::permute_optimized_with_trace` | poseidon2.rs:362–410 | 2 |
| `poseidon2::external_linear_lazy` | poseidon2.rs:188–197 | 2 |
| `poseidon2::internal_linear_lazy` | poseidon2.rs:224–232 | 1 |

The constants' original spans are `/rustc/library/core/src/slice/mod.rs`
1041:4–1043:5 (immutable) and 1061:4–1063:5 (mutable). The Charon diagnostics
show failed conversion of scalar address `0x4` with pointer types
`*const [u32;16]`, `*mut aspis_core::field::M31`, and
`*const aspis_core::field::M31`. `DanglingIntPointer` is reported by the
extractor's constant converter; this is **not** a checked runtime Rust
counterexample. `unsupported-constants.json` records exact function IDs 7,
18, 21 and all original/generated spans; `full-closure-functions.json`
records the relevant source bodies and dependency declarations.

The closure is records → pair_trace::pair_empty_roots (pair_trace.rs:217–224)
→ pool_v1_tree_parent / poseidon2::merkle_node_compress_v3 (495–504)
→ permute_optimized_with_trace and its lazy linear layers. The concrete
closure includes 268 declarations, not merely an opaque assumed root table.

## Minimal next change needed, not applied or proved

Clear these outside helper paths, or supply extractor support for the
unsupported pointer constants. A source-level candidate is replacing the
slice iterator paths in the two EXTERNAL_INITIAL/EXTERNAL_FINAL traversal
loops of permute_optimized_with_trace, the chunks/iter_mut paths in
external_linear_lazy, and the slice iter/map/sum path in internal_linear_lazy
with equivalent indexed while loops. The rewrite must preserve all state
values and round/trace callback order. It would touch three other functions
in poseidon2.rs and requires new authorization; no such edit, extractor
patch, type/signature change, repin, or proof claim was made. This candidate
is only a minimal pattern-level proposal for the observed constants; further
FnOnce or arithmetic/extraction blockers may remain after it.

An alternative is a fully proved nominal helper link to the already proved
21 cells. No such missing link is assumed here. This failure is not a claim
that every pinned configuration or every behavior-preserving records body is
impossible.

## Separate mapper-isolation result

Keeping pair_empty_roots opaque avoids the concrete-child failure but does
not produce R_shipped: the current pure, fixed-array records body times out
at 240 s in optimized, built, strict-join, and monomorphized configurations.
A structural inspection of built LLBC finds 828,400 StorageDead nodes;
pinned Charon's finish_translation/insert_storage_statements.rs:111–174 adds
missing deads at every abort/return. Omitting explicit drop options and the
Rust RemoveStorageMarkers pass do not solve that post-MIR expansion. No
Charon/Aeneas source or binary was modified. Full attempts and manual stops
are in receipt-index.json; large LLBCs remain hashed on the private host.
