# R439 group projection: independent byte and structure audit

This audit compares the frozen R438 generic-closure LLBC with the lead's R439 group projection. It parses only the JSON structure and scans the exact raw byte span of `translated.ordered_decls`; it does not translate, execute, or interpret Rust semantics.

The source LLBC SHA-256 is `76eefed780e23eb3243413b913e935dc7a9b661bceeb0fc0346668621ab07fb6`. The projected input SHA-256 is `d28419f408e6bab79c80859db37e137f4ab62b6bd73c7c5a5d909582308a75b9`. The exact projection generator and its existing receipt are checked against the hashes recorded by the projection process.

The checker verifies that the byte prefix before the ordered declaration array and the complete suffix after it are identical. This preserves all declaration tables and hash-cons data byte-for-byte. It separately verifies that the selected ordered groups are an order-preserving subsequence of the 310 original groups, that the selected set matches the receipt, and that Fun284 is sourced from TraitImpl47 / FnMut trait 9 / method 0 with `reuses_default=false`. The target retains 40 complete groups: 27 functions, 3 globals, 2 trait declarations, 2 trait implementations, and 6 types. The TraitImpl47 row implements trait 9.

Run from the repository root with:

```sh
python3 .r21-scratch/r439-closure-execution-preflight/projection-audit/verify_projection.py
```

The default report is `audit-report.json`. Optional `--source`, `--target`, and `--out` arguments are available, but pinned source and target hashes remain mandatory. No approval receipt is created by this audit. The projection remains an extraction-selection artifact; this proves no callback execution, lifetime, cryptographic, or security property.
