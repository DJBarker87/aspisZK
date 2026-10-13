# Knowledge extractor import narrowing and dependent focused compiles

The only tracked source edit for this task is in
`AspisFormal/AspisFormal/Pool/KnowledgeExtractorInterface.lean`: its import
changed from `Mathlib` to `Mathlib.Data.Real.Basic`. The file's theorem and
definition bodies are byte-identical. Its final source SHA-256 is
`e1eaf2fbc72bfd01506d2129ee3db5761679bf20d764e027054d520a5729152d`.

The four focused targets were compiled in the isolated NUC workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` using
`compile-one.sh`, Lean memory limit 5000 MiB, and separate scopes with
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. Each runner
receipt recorded an existing 24 GiB reservation plus the 6 GiB scope. The
successful source hashes and outcomes were:

| Target | Source SHA-256 | Exit | Wall time | Peak RSS | Swap |
| --- | --- | ---: | ---: | ---: | ---: |
| `AspisFormal/Pool/KnowledgeExtractorInterface` | `e1eaf2fbc72bfd01506d2129ee3db5761679bf20d764e027054d520a5729152d` | 0 | 1.06 s | 1,640,700 KiB | 0 |
| `AspisFormal/Pool/AlgorithmicCircleDecoderV7` | `2faaf875cf3237c9409a19bf2bbb2dd3d302288ed24b059aabb90fac5ddd6471` | 0 | 1.49 s | 2,764,528 KiB | 0 |
| `Wide/InitialEncoder` | `518bf5e70161f11981f3c0b97f95f88efe08e0d3065d54848079e507138552b2` | 0 | 1.25 s | 2,748,088 KiB | 0 |
| `Wide/FinalEncoder` | `6ae59a2d5f9d2d5d56b70ac6c67121d3bcb26f42470bafb3e2d798429590488f` | 0 | 2.10 s | 2,771,808 KiB | 0 |

The unchanged dependent source hashes above are from the local worktree. Their
corresponding isolated output `.olean` SHA-256 values are, in the same order:

```text
64797f855c4c38a5298de8107c1f0f9ee044ef0785a401d1c58126893af7be35
9b7037e6d6a862ede245c926269ba40dbf07c78eb3e1e444407cb80f1db2948c
dae8893ca440230344d8a0eca8c903100a73023a783b83780145692e30230fa9
4481735d5c6e40ac75a6b68e4857bfbdcd460ade9fadb0d43510b32941bd7110
```

The decoder target printed 16 axiom audits; each used only `propext`,
`Classical.choice`, and `Quot.sound` (one theorem used only `propext`). The
initial encoder printed four audits with those same standard axioms, and the
final encoder printed four audits with those same standard axioms. The
`KnowledgeExtractorInterface` source contains no `#print axioms` command, so
its successful compile output records no theorem-specific axiom audit.

The first `AlgorithmicCircleDecoderV7` attempt exited 1 in 0.23 seconds at
548,376 KiB because Lean resolved the first namespace root under the isolated
`objects/` and the required `V6OneFoldParameterAudit.olean` was not staged
there. The object existed in the geometry and generic caches. Root then built
the authorized isolated union cache (1521 links) and made the runner unlink
cached target symlinks before writing. Attempt `b` compiled the identical
source successfully. Both attempts and their exact logs/time/hash receipts
are preserved.

Environment manifest SHA-256:
`d2f7294550dbdd9aa1cab186f25809c1a8b5a84d2fef74e3b3234052ced16c12`; Lean
revision `8c9756b28d64dab099da31a4c09229a9e6a2ef35`. The local base revision
was `2df5bf1a6f296a09cff71a886185112b66f0235a`, plus the one uncommitted
import line change. The runner script SHA-256 was
`98fa678c43647e6935f1c67bcacc03a546aeef831e70d7dcd2fbee0d116309d4`.

Exact source snapshots, runner/environment snapshots, receipts, outputs, and
`/usr/bin/time -v` logs are retained under `remote-evidence/`.
