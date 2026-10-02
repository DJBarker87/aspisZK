# R419 mechanical LLBC comparison draft

This is a preparation-only audit design. It does not read or transform a candidate artifact yet, run Charon/Aeneas/Lean, or decide source correspondence. `compare_llbc.py` takes the immutable R396 LLBC, a candidate LLBC, and an optional exact edit manifest. With no manifest, no differences are permitted. With a manifest, it applies only individually guarded JSON-path `replace_exact` and `drop_list_item_exact` operations to an in-memory copy of the original and compares the entire decoded candidate tree. Any unlisted change—including body/control-flow, error variants, source metadata/attributes, declaration order, or unrelated types—remains in the diff and makes the result fail.

The script decodes Charon's `HashConsedValue` / `Deduplicated` wrappers structurally before comparing. It does not globally discard fields named `generics`, `type`, `ty`, `body`, `span`, or similar. The empty allowlist behavior is the only validated policy in this draft; no normalized comparison has been run. The manifest validator is deliberately strict and is not yet a statement that any particular substitution or binder/argument deletion is valid.

## Frozen baseline and inventory

- Original LLBC: `docs/research/v8-full-view-zk-20260912/evidence/r405-generic-batch-translation-frontier/provenance/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc`
- Original SHA-256: `399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae`; R418 records `has_errors=false` and 430 hash-cons entries.
- R418 census: `.r21-scratch/r418-binder-substitution-preflight/decoded-reference-census.json` (bound by `inventory.json`). It enumerates constrained function binders Fun58/120/169, five direct function refs with arities 5/6/5 as appropriate, the Iterator method36 binder, four impl method36 binders, and four trait dispatch calls with three method type arguments.
- R419 lead contract currently proposes substitution in the selected constrained binder(s), elimination of the corresponding parameter and reflexive constraint, and exact call-site argument deletion. This audit draft does not endorse that proposal; the lead must supply the final exact paths, before/after values, complete census, and acceptance rules.

## Limits and next input

No transformed/candidate LLBC was present in the inspected R419 directory when this draft was prepared. Therefore this bundle contains no original-versus-candidate mismatch report and makes no claim that any transform preserved the source. Once a candidate exists and the lead supplies the final path-level allowlist, the script can produce a report listing all remaining nonidentical JSON paths and classifying likely executable/control-flow, source/attribute, order, typed-generic, or other paths. The parent decides admissible edits and whether a later run is authorized.
