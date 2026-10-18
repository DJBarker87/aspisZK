# Exact source audit and declaration re-pin

`exact-refactor-reverse-audit.json` checks approved1d/1e and all adopted1f
source changes, including exact reverse restoration, cfg variants, loop order
and unchanged arithmetic statements.
`candidate-source.patch` is the aggregate two-file production diff from the
lead to candidatea555; `candidate-source-pin.json` records its hash and verifies
source equality at the integration revision. It is the concrete source diff
for the lead's J1.R13 rebuild.

`declaration-repin.json` is the complete read/hash inventory for the explicitly
registered accepted/current extraction universe at
`f11e4f72d6d37c2bba56ea593d6f5b3fa566eca8`, compared with85ef4199b.
The production source is identical to candidatea555. It reports:

- 341 unchanged declarations, with source/context and retained signature hashes;
- 90 re-extracted declarations, with retained raw statement/body diffs and binding audits;
- one previously authorized readonly helper/projection replacement, still conditional
 on the single metadata-projection premise;
- zero unresolved declarations.

The12 file coverage entries distinguish migration-changed files from retained
accepted files outside the selected migration diff. The latter are checked too;
absence from `git diff` is not treated as missing source. Synthetic kit names,
SDK declarations, and historical/rejected LLBC variants are separately inventoried.
An opaque boundary's unchanged signature is explicitly distinguished from its
unproved implementation; both implementation hashes are retained when available.

The current query, semantic rounds and complete verify_finish bound-model audits
replay exact identifier substitutions and explicit binder additions, the five
listed carrier syntax normalizations,19 canonical finish carriers, seven shared
helpers, and five fixed actual-round/equality bodies. The finish record alone
requests an `impl_def`-aware declaration parser. This prevents an unrelated trait
declaration from being silently included in a neighboring function's body.

`declaration-repin-receipt.json` records the exact command, source revision,
checker/runner hashes, exit0,70.341393s wall,612483072-byte peak RSS and zero
swap. #print axioms is N/A for this read/hash-only inventory. No build ran.
`run-declaration-repin.py` retains the measured runner. Reproduction should pin
its recorded source revision rather than silently change the accepted universe.

Two failed inventory attempts are preserved. `inventory-normalization-review.json`
records the rejected old normalization schema and its replacement. The complete
`inventory-seed-scope-rejected/` snapshot records exit2 before the source-scope
fix, including exact metrics and log. Neither failed result is accepted, and no
Lean or native gate was rerun to correct these metadata issues.
