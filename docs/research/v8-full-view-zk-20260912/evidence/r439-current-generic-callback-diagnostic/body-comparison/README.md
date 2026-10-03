# R437 Fun112 vs R438 Fun284 complete callback-body comparison

R437 input SHA-256: `bafe9c1297a8ea92eaea3c37c685da3f5d3fe2e04c335ac9f1f4d64c4312386c`; R438 input SHA-256: `76eefed780e23eb3243413b913e935dc7a9b661bceeb0fc0346668621ab07fb6`.
Embedded `relation_callback.rs` SHA-256: R437 `4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f`, R438 `4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f`.
The exact raw declaration rows and fully hash-cons-expanded rows, including every statement and `on_unwind` subtree, are retained in `raw-and-expanded-fun112-fun284.json`. The structural view omits source-span fields and only the `id` field on recognized statement envelopes; it preserves generics, all region annotations, all other declaration IDs, every operation, and all unwind/drop bodies. A narrowly stated nominal-reference bijection is applied and separately evidenced.

## Nominal declaration ID bijection

|R437|R438|Identity basis|
|---|---:|---|
|Fun24 `aspis_core::field::QM31::mul`|Fun20|Same decoded name path and `QM31 × QM31 → QM31` signature (all inputs/output are Type2); source definition IDs differ.|
|Fun124 `aspis_core::field::QM31::add`|Fun321|Same decoded name path and `QM31 × QM31 → QM31` signature (all inputs/output are Type2); source definition IDs differ.|
|Type50 closure `freeze::closure::2::closure::0`|Type65|Exact same source text and name path, two captured-field struct shape; field types retain Free-region annotations.|
|TraitDecl3 `core::ops::function::FnMut`|TraitDecl9|Same exact trait name path/lang item in decoded declarations.|
|TraitImpl35 closure FnMut impl|TraitImpl47|Same closure source text/method slot and FnMut target after Type50→65; complete impl generics are retained in evidence.|
|Type2 `aspis_core::field::QM31`|Type2|Same ID/name/kind on both inputs; unchanged mapping.|

The mapping evidence, including expanded signatures and declaration rows, is in `nominal-id-bijection-evidence.json`.

## Statements, operations, unwinds, and regions

Each body has 36 statements in its outer list plus three nested lists of five statements each, for 51 total. Each has three `on_unwind` payloads. `body-shape-audit.json` records every nested list path, every operation-kind count, exact unwind paths, and all 31 `Free` region-annotation occurrences with their paths and values. These inventories match after the stated normalization; no region annotation is erased.

## Structural comparison

Differences after the stated normalization and nominal mapping: **1**. Category counts: `{"generics_types": 1}`.
The sole remaining difference is `src.TraitImpl.trait_ref.generics.types`: R437 has two type arguments while R438 has three; the additional R438 argument is `QM31` (Type2), according to both captured Type2 declarations. It is retained as a difference, not normalized away. The 51-statement operation structure, three unwind subtrees, and all 31 region annotations match under the stated normalization.
Every remaining path/value difference is recorded in `structural-diff.json`; `comparison-report.json` groups those exact paths by region/generic, operation, unwind, and other structure. No region indices were normalized or discarded. A zero diff would only mean these JSON callback bodies coincide under the recorded structural normalization; it would not establish runtime semantics or source-to-model correspondence.

No builds, translations, or Lean jobs were run.
