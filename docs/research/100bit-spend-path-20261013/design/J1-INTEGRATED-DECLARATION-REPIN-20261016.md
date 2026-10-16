The current inventory is pinned to `af828dec09343c268990b925f6ace47eff412a94`: 289 unchanged, 52 re-extracted and one authorized helper/projection replacement, with zero unresolved correspondence in the registered accepted/current cones. Read [the Prepared/tx1 addendum](J1-PREPARED-TX1-REPIN-ADDENDUM-20261016.md) for exact accepted prefixes, source layouts, statement/binder audits and the boundary/exclusion ledger.

Regenerate at the final integration ref, then compare the exact report:

```sh
python3 -B docs/research/100bit-spend-path-20261013/tools/j1-integrated-declaration-repin.py --revision FINAL_REF --require-complete
python3 -B docs/research/100bit-spend-path-20261013/tools/j1-integrated-declaration-repin.py --revision FINAL_REF --check --require-complete
```

The checker reads Git blobs, archive metadata and generated text only. It invokes no compiler, Lean, runtime harness, SBF, RPC or build host. Every input is hashed; current generation uses no supplementary paths. `--output` selects another report. `--migration-before` defaults to `ca137f5db`. Optional `--additional-cone` manifests explicitly register another accepted cone; a successful LLBC bit alone does not confer acceptance.

Source membership is determined from retained metadata and verified historical layouts before current-text lookup. Exact Rust body and enclosing context hashes are checked separately from generated/LLBC signature hashes. Missing or ambiguous correspondence is reported, not discarded. These are source/generated-statement identities, not current compiler name-resolution, account custody or runtime-refinement theorems.

The earlier report/check receipt and 268/21/1 checkpoint remain in Git history. The new report preserves those original classifications and adds the explicitly accepted Prepared and tx1 cones. Signature-only boundaries and LLBC-only metadata are labelled as such. The old AccountInfo wrapper is still an authorized helper-plus-single-conditional-projection replacement, not a newly emitted wrapper implementation. Custody and all remaining caller/provenance gates stay separate.
