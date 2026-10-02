# R388 `reduce_u62` declaration ordering metadata

R388 takes the exact successful R387 LLBC (`fdb448185f0f077cf0df303709da52a8be05eeb800767a4ea9a03f7f3c71afc4`) and changes only `translated.ordered_decls`. The ordered artifact is `R388ReduceU62Ordered.llbc`, SHA-256 `95480c0a8938629f770f7c381fe61a71f44e8275fe2e7275e9edfd4a4bb7f040`. It contains these IDs in dependency-first order: Type0 (`M31`), Fun2 (`P` initializer), Global0 (`P`), Fun1 (`reduce_u64`), Fun0 (`reduce_u62`).

The dependency census found Fun0→Fun1 and Type0; Fun1→Global0; Global0→Fun2. There are zero missing references, unknown typed references, or cycles in the reachable closure. The generated audit records the full integer-reference census and canonical row hashes. The independent checker recomputes the graph, verifies every dependency precedes its consumer, confirms every target row and confirms full JSON equality after removing `translated.ordered_decls`; it passes.

The ordering generator is based on the pinned Charon `reorder_decls` source SHA `8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632` and the R284 metadata-only ordering procedure. This graph is Type/Fun/Global only; no trait rows are reachable. Declaration bodies, signatures, generics, attributes, source spans, options, types, global initializers, and raw LLBC fields are preserved. The proof of preservation is structural JSON equality, not source semantics.

`translation-plan.json` specifies a future focused translation using the retained R363 Aeneas executable (SHA `3dc9ad6de1af901c8ead41940ba97097a0cf06f82d27dbc7d7c5eac03695e329`) under 5/7 GiB, zero swap, 128 tasks and namespace `AspisR388ReduceU62`. It is a plan only: no translation or template filling was launched, and no Lean compilation was run. Lead review/authorization is required before launch.


## Authorized translation outcome

After review of the ordering audit and plan, one translation ran with the R363 executable. The first launcher attempt failed during a preflight-only memory check before invoking Aeneas; its log, launcher, and receipt are preserved under `history/`. The regex was corrected, the existing remote directory was verified to contain only the exact input LLBC, and the single authorized translation then exited 0. The generated output hashes are recorded in `translation-output-audit.json`.

The generated `M31.reduce_u62` body is preserved byte-for-byte in `generated-reduce-u62-definition-verbatim.lean`: it calls `reduce_u64` and returns that result. The R387 LLBC’s explicit false-guard assignment and corresponding branch are preserved as parsed AST nodes in `raw-release-debug-assert-branch.json`; the generated release body contains no assertion. This is a structural record only. No Lean compilation, template filling, source-correspondence claim, or caller range proof was performed.

Translation took 0.23 seconds with GNU-time maximum RSS 57,024 KiB and zero swaps. The systemd wrapper separately reported 308 ms service runtime, 328.0K `Memory peak`, and 0B swap peak; those wrapper metrics are retained separately from GNU-time process RSS.
