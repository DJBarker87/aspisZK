# R254 `C::input` dependency frontier

Read-only inspection of the exact R245 Charon 0.1.223 serialized LLBC and the existing pinned Charon reorder excerpt. No translation, build, patch, or Option semantic substitution was attempted.

## Exact leaf and source

R245 declaration `FunDeclId 6` is `aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C::input`; local source file id 0, `r110_norm.rs`, span line 24 columns 4–77. Its LLBC `item_meta.source_text` is:

```rust
fn input(x:CM31)->Option<Self>{Some(Self(B::input(x.a)?,B::input(x.b)?))}
```

The decoded structured body is present and has statement/expression node IDs up to `320`; it represents both `?` operations, with the two branch/residual arms. It has a normal structured body (not an opaque/absent body). The literal direct function references in this body are `FunId 0` (`B::input`, twice), `FunId 21` (`Option<T>::branch`, twice), and `FunId 22` (`Option<T>::from_residual`, twice). No direct global reference occurs in Fun6. The generated `Try` branch and `FromResidual` paths are explicit in LLBC; this inventory does not replace them with handwritten Option cases. The six call-expression node IDs in Fun6 are 230 (`B::input`), 236 (`Try::branch`), 252 (`B::input`), 258 (`Try::branch`), 284 (`FromResidual::from_residual`), and 305 (`FromResidual::from_residual`), all at file 0 line 24 (columns 45–59 for the first operand and 60–74 for the second).

## Referenced declarations and table coverage

All IDs below are LLBC-local indices in the R245 file. All referenced IDs have rows in the relevant top-level table; the serialized `ordered_decls` array is empty.

| Table | R245 rows | Needed/observed frontier | Coverage |
|---|---:|---|---|
| TypeDecl | 7 (0–6) | 0 `B`, 1 `C`, 2 `aspis_core::field::M31`, 3 `core::option::Option`, 4 `aspis_core::field::CM31`, 5 `core::ops::control_flow::ControlFlow`, 6 `core::convert::Infallible` | Every listed type row exists. |
| FunDecl | 31 (0–30) | Direct from Fun6: 0 `B::input`, 21 `Option::branch`, 22 `Option::from_residual`; Option/Try impl also carries 28 `Option::from_output`. `B::input` has no direct function call; its body references Global0. | All four named helper/function rows exist; bodies are present for Fun6, Fun0, Fun21, Fun22, Fun28. |
| GlobalDecl | 3 (0–2) | Fun6 has no direct global; Fun0 (`B::input`) references Global0 `P110`. | Global0 row exists with serialized initializer/value. Global1 `PP` and Global2 `aspis_core::field::P` are also present in the inherited table but are not direct Fun6 references. |
| TraitDecl | 4 (0–3) | Option helper frontier: 1 `core::ops::try_trait::Try`, 2 `FromResidual`, and 3 `Residual` used by Option’s residual implementation/type. | All rows exist. TraitDecl0 `From` is also inherited. |
| TraitImpl | 4 (0–3) | 1 Option: Try; 2 Option: FromResidual; 3 Option: Residual. | All rows exist. TraitImpl0 `From<u32> for u64` is also inherited. |

The `Option<T>: Try` impl row (TraitImplId 1) lists method function IDs 28 (`from_output`) and 21 (`branch`); the `Option<T>: FromResidual< Option<Infallible> >` impl row (TraitImplId 2) lists function 22 (`from_residual`). These method IDs resolve to present FunDecl rows. The `Residual for Option<Infallible>` impl (TraitImplId 3) is also serialized. The foreign/core trait and impl rows are inherited context in this R245 artifact, not evidence that R245 selected each one as an independent source root.

No required item row or method function reference in this inspected frontier is absent. But every TraitDecl and TraitImpl `vtable` field in this artifact is `null` (including required Option `Try`, `FromResidual`, and `Residual` rows). TraitDecl method entries are signature/method descriptors and do not provide vtables; Try and FromResidual trait method `default` slots are serialized as `null`, while the implementation method IDs above are populated and resolvable. The three Option helper declarations have structured bodies; they are not missing helper bodies. The serialized global initializer/value records are present rather than null. The two local named constants P110 and PP and the imported P global have serialized `value` fields; the required P110 initializer is not null. No extra init function is inferred beyond serialized values.

## Pinned Charon dependency/order behavior

The existing R237 excerpt is from pinned `charon/src/transform/add_missing_info/reorder_decls.rs` (source SHA-256 `8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632`). Its `DepsForItem` visitor uses `translated.get_item(tgt)` before queuing a dependency or adding an edge; absent targets are therefore not fabricated into the order graph. It suppresses a reference from an item to its own parent TraitImpl or TraitDecl, with comments explaining this avoids mutually recursive method/impl or method/trait groups around associated types. It also skips generic traversal of `ItemMeta` and `ItemSource`.

There is a separate `compute_declarations_graph` path for function declarations: it visits function DefId, generics, signature, and body, then explicitly inserts an edge to the trait declaration only when the function’s `src` is `ItemSource::TraitDecl`. Fun6 is `TopLevel`; Option helpers Fun21/Fun22/Fun28 have `TraitImpl` sources, so that special TraitDecl source edge does not apply to these functions. A method's `TraitImpl` source edge is likewise suppressed as parent-trait-impl metadata.

For a TraitDecl item, the visitor visits generics, parent clauses, associated types, vtable, associated-const types, and trait method parameters/signatures. It does not visit default method bodies as part of the trait declaration. When a default method ref exists, it `insert_node`s the default function and visits its generics; the implementation source and actual function body remain associated with the function declaration. TraitImpl items use ordinary item AST visitation, including its methods/vtable refs. These distinctions matter for an ordering pass: direct method signature dependencies, default method nodes, actual function body refs and implementation-local refs are not interchangeable sources of edges.

The source excerpt demonstrates only the pinned reorder algorithm mechanics. This report does not define or implement a replacement ordering pass.

## Hashes and provenance

- R245 raw serialized LLBC: SHA-256 `59412a374a2753759103071c7190ac6587249517b0f991e619afc8a12a93e197`.
- R245 `decoded.json`: SHA-256 `f620d8de019fb1050b9cf2c9259ad75924b0fb313f93463c39f5fd0d8fadbdec`.
- Existing pinned Charon dependency/reorder excerpt: SHA-256 `f7c7528535f5d7aa77851cbb18f9f36beab7e5ddb40e7aa25c4ca85704b33259`; excerpt records implementation source SHA above.
- Existing R233 reorder excerpt: SHA-256 `9d8a38f59dc75acbcdbcdd707172619c1c1fc8703ed8238010d3d105cf791563`; records the same reorder source SHA.
- R245 campaign result records Charon exit 0, artifact hash above, and frozen source hashes in `.r21-scratch/r245-r110-leaf-extract/result.json`.
