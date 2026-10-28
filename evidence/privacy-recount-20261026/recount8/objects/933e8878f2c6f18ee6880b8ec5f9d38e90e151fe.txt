# Stop under D274 bounded repair rule

The copy at records:229 clears the historical InterpAbs.ml:1955 failure.
Charon `pv14-records-charon-01` exits 0 with `has_errors=false` and the
records implementation body present. Pinned Charon, driver and Aeneas hashes
match runjoin13; extraction preflight is enabled and passes.

Aeneas `pv14-records-aeneas-01` (strict joins, sequential) exits 2:

```
Unsupported operation: ub_checks<bool>
Source: '/rustc/library/core/src/iter/range.rs', lines 984:4-986:5;
macro source: '/rustc/library/core/src/ub_checks.rs', lines 77:34-77:41
Compiler source: interp/InterpExpressions.ml, line 1512
```

The LLBC embeds this intrinsic in records via the existing `for level in
0..24` at pair_forest_copy_builder.rs:233, whose range-next body has been
inlined by the same optimized MIR settings as runjoin13 Charon02.
The original pair selected-second borrow failure is no longer reached.
No Lean implementation was generated or accepted; no R_shipped is defined.

Minimal proposed source repair for this obstruction: replace that existing
range-based `for` with `let mut level = 0; while level < 24 { ...;
level += 1; }`, preserving the 24 bodies and order. This is an iterator-loop
rewrite, neither borrow-to-copy nor removal of one of the previously
authorized closures/combinators. It is NOT applied. No extractor modification,
intrinsic stub, assumed result or changed compiler flags is used to bypass it.
This identifies a blocker for the tested pinned extraction configuration,
not a proof that every possible extractor configuration must fail.

Separately, raw remains opaque in this isolation. Its unchanged from_fn
closure still needs a concrete helper connection (runjoin13 direct extraction
failure retained); opaque isolation is not a complete shipped extraction.
The 21 mathematical empty-root cells remain proved but cannot substitute
for the missing records extraction or its source association.

Per the prompt's explicit stop condition, further proof stages stop here;
Lean/Kani budgets are unspent, not exhausted. Gate (a) must still finish for
the committed one-line shipped repair. Gates (b)/(c) remain lead-owned.
