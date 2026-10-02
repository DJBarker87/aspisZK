# R268 ordering generator attempt

`order_metadata.py` implements a fail-closed metadata traversal from the exact R266 roots Fun0 and Fun1, guided by pinned Charon `DepsForItem`. It skips item metadata and item source during normal typed traversal, uses Charon's explicit Fun-from-TraitDecl source edge, and has dedicated TraitDecl handling for parent clauses, signatures, defaults and their generic references. It records typed-reference census and dependency edges, and changes only `translated.ordered_decls` after closure/order checks pass.

The first generator run stopped at a missing emitted declaration reference: `TraitDecl[0].vtable.id` is `Adt 5`, but there is no Type declaration row with id 5. `item_names` identifies Type5 as `core::iter::traits::iterator::Iterator::{vtable}`. Pinned Charon's `insert_edge` only enqueues a target if `translated.get_item(tgt)` exists; the supplied task also requires this generator to fail closed on missing refs rather than omit them. The diagnostic is retained in `failure-diagnostic.json`; no ordered LLBC output or audit was emitted. Lead review is needed to decide whether this vtable pseudo-type is to be treated under Charon's absent-item filtering rule or as an error frontier.

The generator intentionally did not proceed to later graph nodes after this failure. No SCC policy was added. No translation or Lean action was run. The exception is not evidence of source or theorem semantics.

Pinned reorder source SHA-256: `8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632`.
Input LLBC SHA-256: `f4ed281e203e81208acf5c9cbae790d6a15e6ae5c7d5367d21a683768d0bb4a9`.
Generator SHA-256: `e38ed783071a2bd448f79db22ecf3e0d396fa4563ecae1993fa0e339ae62443d`.
