# Charon inherent-method root matcher finding

Pinned Charon source: `name_matcher_mod.rs`, copied from `/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon/charon/src/name_matcher/mod.rs`, SHA-256 `c9ac2cb3b5c868da191f77a185868c635ff574ab3e02bd97fac95b12e7796da6`.

At lines 268-270, `PatElem::matches_with_generics` handles inherent implementation paths with:

```rust
(PatElem::Impl(_pat), PathElem::Impl(ImplElem::Ty(..))) => {
    // TODO
    false
}
```

Therefore the otherwise plausible start pattern `crate::weights::Weights::pair` does not seed the dependency graph used to compute `ordered_decls`. The LLBC still contains declaration records (`fun_decls=340`, `type_decls=91`, `has_errors=false`) but `ordered_decls=[]`; Aeneas then emits an empty `translation.json` and header-only Lean files while returning exit 0. This is retained as a negative backend control, not accepted extraction evidence.

The changed module-prefix root `crate::weights` is a parser-valid prefix and seeds the graph without changing Rust source. Its LLBC has 338 ordered declaration groups, `fun_decls=385`, `type_decls=96`, `has_errors=false`; the source coverage report checks the exact `Weights::pair` and three extracted helper source spans. Aeneas on this corrected LLBC has not run yet because the fresh 4-GiB admission was denied at 48.375 GiB existing finite reservation. No memory-cap reduction or job bypass was attempted.
