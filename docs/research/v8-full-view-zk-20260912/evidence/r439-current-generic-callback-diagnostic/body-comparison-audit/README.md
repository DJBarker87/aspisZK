# Independent R439 callback-body comparison audit

`verify_body_comparison.py` reads the two saved native LLBC captures and independently expands their `HashConsedValue`/`Deduplicated` rows for R437 Fun112 and R438 Fun284. It confirms capture hashes `bafe9c…2386c` and `76eefed…07fb6`, matching embedded `relation_callback.rs` hashes `4f8f80…9820f`, and `has_errors=false` for each.

It checks the exact captured source references: R437 points to TraitImpl35 / FnMut TraitDecl3 / method0 with `reuses_default=false`; R438 points to TraitImpl47 / FnMut TraitDecl9 / method0 with `reuses_default=false`. Each capture's TypeDecl2 is named `aspis_core::field::QM31`. Its `aspis_core::field::QM31::{mul,add}` inherent definitions have two input types and output all resolving to that capture's TypeDecl2. This records declaration/signature identities, not execution behavior.

The script independently applies the explicit nominal reference map and checks its canonical rows against the saved views. The map edits only recognized declaration/reference ID fields. It ignores source-span fields and `id` fields on recognized structured-statement envelopes; it does not remove or rewrite generic/region fields. The report records every nominal mapping edit path/value and all 31 region values/paths on each side. Both bodies have 51 statements, three unwind payloads, matching operation counts, and matching region annotations.

After normalization the only difference is at `src.TraitImpl.trait_ref.generics.types`: two arguments in R437 versus three in R438. The added R438 argument is the TypeDecl2 QM31 type. It remains an explicit difference. The report and retained raw/expanded rows do not claim source execution, borrow/alias equivalence, trait dispatch, ABI correctness, or semantic correspondence.

Run from the worktree root:

```sh
python3 .r21-scratch/r439-closure-execution-preflight/body-comparison-audit/verify_body_comparison.py
```

This is a read-only structural audit; no capture, translation, build, or Lean job is performed.
