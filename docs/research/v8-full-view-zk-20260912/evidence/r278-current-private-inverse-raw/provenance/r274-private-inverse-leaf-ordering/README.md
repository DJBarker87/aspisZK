# R274 private inverse declaration ordering

This metadata-only generator starts from the exact R266 roots Fun0 and Fun1 and follows the pinned Charon `DepsForItem` visitor rules. It emits no source bodies and changes no declaration rows: its sole LLBC mutation is `translated.ordered_decls`. The full ordered closure contains 34 declarations: 6 Type, 15 Fun, 3 Global, 5 TraitDecl, and 5 TraitImpl. `audit.json` retains the full 54-edge dependency graph, 309 typed-reference census entries, reachable trait defaults, and integrity checks.

The lead authorized mirroring pinned Charon's `get_item` filter only for absent IDs in explicit `TraitDecl.vtable` or `TraitImpl.vtable` metadata. Three such references were skipped and recorded with exact source path, target ID, absent-row status, and `item_names` label:

- `TraitDecl[0].vtable.id` → Type5, `core::iter::traits::iterator::Iterator::{vtable}`
- `TraitDecl[19].vtable.id` → Type43, `core::cmp::PartialOrd::{vtable}`
- `TraitDecl[20].vtable.id` → Type44, `core::cmp::PartialEq::{vtable}`

No other absent references were skipped. The generator fails closed on other missing references, unknown typed-reference shapes, or dependency cycles. It found no cycles or unknown shapes for this input. Charon may still report a diagnostic if the ordered artifact is passed to a translator; the ordering metadata is not evidence of successful translation, source correspondence, or a semantic theorem.

The prior R268 stopped attempt remains unchanged in `.r21-scratch/r268-private-inverse-leaf-ordering/`, including its initial failure at Type5. The first R274 generator/audit/output set, before the label guard was enforced, is preserved in `rejected-metadata-before-label-guard/`.

Input R266 LLBC SHA-256: `f4ed281e203e81208acf5c9cbae790d6a15e6ae5c7d5367d21a683768d0bb4a9`.
Pinned reorder source SHA-256: `8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632`.
Generator SHA-256: `e8caf7f1d31e153e9b9dce6c455b4655c399b2fb2df422f4d5099413fca3df33`.
Ordered output SHA-256: `fb316e998775a411073d19667a06a15647af4cc9599188d7061596259b211768`.
Audit SHA-256: `87bf26064ef0ee320412ce906d5908296eae879909500938586e492cbba514b1`.
