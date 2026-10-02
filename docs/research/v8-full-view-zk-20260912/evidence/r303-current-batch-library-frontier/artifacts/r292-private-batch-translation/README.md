# R292 original R283 batch translation

This one-time Aeneas translation consumed the byte-identical original R283 LLBC
(SHA-256 `999fdb4f5a034faf9d4aa11c7a44851b9c79f471d76ae6afb3b92aed0767c8d5`,
`has_errors=false`). It did not use the failed R288/R290 subset-ordering
outputs. The exact root was `Fun 0`, local with a non-opaque body, and the
original `ordered_decls` entry at index 107 is `Fun NonRec 0`. The output
namespace is `AspisR292PrivateBatch`. The Aeneas binary hash is
`63b04a88532b8fb0aaa0d274881b5cacf00bc4f449243ece905178f0de9cc495`; the
recorded worktree revision is `380c7d46c9719dcfcab601fac2607861d47dee02`.

The capped command used the pinned host workspace and the saved `-sequential
-no-progress-bar -abort-on-error -backend lean -split-files -emit-json`
settings in `translate-command.json`. It ran in the dedicated
`aspis-r292-private-batch-translation.service` with MemoryHigh 5G, MemoryMax
7G, MemorySwapMax 0, and TasksMax 128. Preflight observed 55,215,392 KiB
MemAvailable and R289's 7 GiB/zero-swap reservation. GNU time reports exit 0,
wall 1.03 s, peak RSS 143,968 KiB, and zero swaps. The full translator and
launcher logs are retained.

The translator exit status was 0 and it emitted the batch root: the manifest
entry is `AspisR292PrivateBatch.circle_norm.joined_inverse.line_norm.r110_norm.batch`
in `Funs.lean`, whose definition is at line 493. The first postflight root
scan searched for a namespace prefix that generated Lean omits inside its
opened namespace; that initial false negative is preserved in
`translation-result.initial-root-scan.json`. `postflight_audit.py` corrected
the inventory by matching the `translation.json` entry and emitted `def`.

Aeneas printed three warnings that builtin information was unavailable for
Iterator `chain`, `any`, and `rev`. It emitted five function holes in
`FunsExternal_Template.lean` (`Iterator.any.default`, `Iterator.chain.default`,
`Chain.Iterator.next`, slice `Iter.any`, and `Slice.last`) and one `Chain` type
hole in `TypesExternal_Template.lean`. These remain unfilled template axioms;
no Lean file was compiled and no external assumption was accepted. Root
emission is recorded separately from translator exit status and from these
outstanding external-template obligations.
