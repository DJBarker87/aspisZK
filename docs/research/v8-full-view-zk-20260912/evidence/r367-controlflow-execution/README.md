# R367 ControlFlow execution evidence

This bundle records the byte-preserved R364 generated ControlFlow modules, the approved import-only normalization, one explicitly qualified discriminant projection, and three focused Lean execution lemmas. `inventory.json`, `copy-graph.json`, `verify_evidence.py`, and `SHA256SUMS` are self-contained relative to this directory; the verifier does not read `.r21-scratch`, SSH, or a build-host path. `pinned-aeneas/source/` contains the relevant full source files copied from the pinned Aeneas tree, and `pinned-aeneas/import-preflight.json` records their origin, hashes, module-presence observations, and import rationale.

`generated-original/` keeps the exact R364 `Types.lean` and `Funs.lean`. Their source transformations reconstruct byte-for-byte as the promoted files: replace only the umbrella `import Aeneas` line with `Aeneas.Std`, `Aeneas.Extract.Extract`, and `Aeneas.Data.Discriminant`; append the listed complete `#print axioms` commands; and, in Funs only, qualify the one `read_discriminant` projection as `Aeneas.Std.read_discriminant`. All generated declarations, `rust_type`/`rust_fun`/`discriminant` attributes, constructors, assertions, and results remain intact. Original failed inputs and logs are retained in `staging-history/attempts/`.

The saved translation result records R364 exit 0 on LLBC SHA-256 `8b9bd55e374866294b591758e1282d08998cb002e30b070207156b61f81a69ca`, with Lean compilation marked false. The static census copies the generated source and metadata and finds function IDs 37/39/40 and the three emitted ControlFlow types; it is an inventory, not a semantic check.

The three green focused checks used the pinned cached Lean 4.32 workspace, `-j1 -M4500`, systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`:

| Target | Exit | Wall | Lean-child peak RSS | Swap |
| --- | ---: | ---: | ---: | ---: |
| `AspisR364ControlFlowPattern/Types.lean` | 0 | 1.07 s | 2,539,084 KiB | 0 |
| `AspisR364ControlFlowPattern/Funs.lean` | 0 | 1.01 s | 2,528,224 KiB | 0 |
| `R367ControlFlowExecution.lean` | 0 | 1.02 s | 2,530,812 KiB | 0 |

All full successful `#print axioms` output is in the saved logs. The three ControlFlow types and native Infallible report no axioms. `branch_exact` and `from_output_exact` report no axioms; `from_residual_exact` reports `propext`, `Classical.choice`, and `Quot.sound`. None of the successful reports includes `sorryAx`. Four failed attempts are preserved as history, including the unqualified-helper name-resolution failure and two early proof-plumbing drafts; failed-run `sorryAx` output is not treated as a successful result.

The residual theorem uses the emitted `ControlFlow<(), Infallible>` and eliminates its impossible `Continue` payload in the Lean model. It does not establish a Rust source-level guard, caller chronology, iterator/chain/any/fold behavior, callback correspondence, privacy, soundness, or compiler correctness. The promoted files are still scratch candidates pending lead review; this bundle does not imply a commit or release decision.
