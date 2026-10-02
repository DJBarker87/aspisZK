# R267 private inverse ordering frontier

This is a read-only inventory of the failure in the metadata-only ordering generator. The input is the R266 decoded full-LLBC artifact; no translator, generator, Lean target, or build was run for this inventory.

The two exact roots are `FunId 0` (`r110_norm::B::neg`) and `FunId 1` (`r110_norm::B::inv`). Their reachable local field path includes `FunId 3` (`M31::inv`) and `FunId 9` (`field::square_n`). The R267 generator reaches `Fun9`, then rejects trait-reference fields while scanning its structured body. This is a generator coverage limitation, not a missing declaration: every referenced trait declaration/implementation below is present in the R266 table.

At `Fun9` body statement 7, the range expression is represented by a `Range<usize>` and invokes `Fun12` (`IntoIterator::into_iter`, `TraitImplId 0`) and `Fun13` (`Iterator::next`, `TraitImplId 1`). The generic references include `TraitImplId 2`, the `Step for usize` implementation, and `TraitDeclId 1` (`core::iter::range::Step`). `Fun13` is sourced from `TraitImplId 1`, whose `impl_trait.id` is `TraitDeclId 0` (`Iterator`). `Fun12`'s `src` records `TraitImplId 0` and `TraitDeclId 2` (`IntoIterator`); the pinned Charon reorder visitor skips item source metadata, so this source provenance should not be mistaken for a body dependency. `Fun9` also calls `Fun7` (`M31::mul`) at statement 9.

R266 contains `TraitDeclId 0..24` and `TraitImplId 0..10`; the required rows are present: `TraitDeclId 0` Iterator, `1` Step, `2` IntoIterator; `TraitImplId 0` IntoIterator, `1` Iterator for `Range<A>`, and `2` Step for `usize`. TraitImpl2 also contains implied references to TraitImpl4 and TraitImpl5; those rows exist. TraitImpl1 has vtable Global4, TraitImpl0 has vtable Global3, and TraitImpl2 has a null vtable. Thus a Type/Fun/Global-only ordering walk cannot close this frontier as written. This inventory does not recommend treating trait metadata as executable declarations or deciding how the lead should handle it.

The existing R156 translated `M31.inv` body uses `massert (self != 0#u32)`, and translated `square_n` is expressed with `Range`, `IteratorRange.next`, and the Aeneas `loop` combinator. Those spellings are visible in the pinned generated file; the Aeneas implementation/mapping source for `massert`, panic, and range iteration was not located in this worktree, so no claim is made about which raw Rust constructs are builtin-mapped. The R156 file is an existing translated reference only, not a new source-correspondence argument.

## Evidence hashes (SHA-256)

- R266 raw LLBC: `f4ed281e203e81208acf5c9cbae790d6a15e6ae5c7d5367d21a683768d0bb4a9`
- R266 `decoded.json`: `1e9332b4276d55a1f55b4116d294ebec62fca3bf41dae44cf955708d186ab40f`
- R267 `order_metadata.py`: `4fa4282cfdf75e45fa7d93cefdf9e434c2977ce0e21f942cc44f27d2c8368fea`
- pinned R156 `FunsCore.lean`: `5ef8405549c6feff405715a6697ffff9a370610d5dc116fc452a1046fae0c1f2`
