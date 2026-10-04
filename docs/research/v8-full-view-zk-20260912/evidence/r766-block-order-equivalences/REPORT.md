# R724 literal block-order index maps and R766 equivalences evidence

This bundle contains the exact source snapshots, full compile logs, receipts, generator inputs, and tool/cache hashes for the literal `Fin 222` block-order maps and their scalar inverse identities. It is a proof of index-map identities only. It does not establish block coefficient correspondence, a source-verifier matrix identity, rank, or security.

## Pinned inputs and construction

- The index inventory input is pinned by SHA256 `268e05932211ba21ebdb9d774a58e53f38ed21ef42dc417da8b6d866b175a48e`; the underlying certificate is `d170dc15f81b0aac68da6cb9291e9907ad72e1738cf3a6b6fd7faf9e32a951f4`; the raw matrix metadata input is `91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af`. Copies are in `inputs/`.
- `rowOrder` is flattened `rows_original` (flat block position to original row ID); `rowOrderInv` is the inverse table. `colOrder` uses flattened columns after mapping original columns back through `selected_columns` into the selected/minor index space; it does not cast the raw 241-column indices to `Fin 222`. `colOrderInv` is the inverse table.
- Python generator checks the exact input hashes, length 222, full permutation coverage, and the inverse tables before emitting the literal `Fin 222` match definitions. The generator `--check` passed for maps and for R766 consumer generation.
- Chunk facts cover indices 0–221 in chunks of at most 32. Case0 establishes row-left and col-left at index zero. Chunk00 reuses those facts and proves the other two zero facts plus all four facts at 1–31; Chunks01–06 cover the rest. The facts are per-index scalar table checks.

## Successful targets

| Target | Source SHA256 | Source revision | Exit | Wall | Peak RSS KiB | Swap | Axiom audit |
| `AspisV8R19/R724BlockOrderMaps.lean` | `678b4a2a53ad1fa75f0c6bdb78f57c7eb385e5b71f18dc1f0dca451f155280e1` | `f5a8c3e2f0751c5d980ae5fb539552a83ea68c3d` | 0 | 0:01.29 | 506256 | 0 | definitions only; no theorem axioms |
| `AspisV8R19/R724BlockOrderCase0.lean` | `829cc0ded4c5821cffb717fb8af495a8076f899d942271151f18531d1e8b8391` | `f5a8c3e2f0751c5d980ae5fb539552a83ea68c3d` | 0 | 0:00.18 | 481400 | 0 | 2 declarations; all `[propext]` |
| `AspisV8R19/R724BlockOrderChunk00.lean` | `c87187aaa4bb88bc554df0315abffa5e4ccc30c02e586cfbf6ccf502f3dfc99d` | `ae1563fcfa831567550e9f3fe8f69d357e16631c` | 0 | 0:01.12 | 490204 | 0 | 126 declarations; all `[propext]` |
| `AspisV8R19/R724BlockOrderChunk01.lean` | `a8b13833ae848823f388703052228784b64552def5587a7ae1c34ddef0f2a128` | `ae1563fcfa831567550e9f3fe8f69d357e16631c` | 0 | 0:01.29 | 490724 | 0 | 128 declarations; all `[propext]` |
| `AspisV8R19/R724BlockOrderChunk02.lean` | `cc1b9cf3e40e9f976a5052c9567d48e75ccf91c38f140762c5ddfe112f47f5a7` | `ae1563fcfa831567550e9f3fe8f69d357e16631c` | 0 | 0:01.57 | 491528 | 0 | 128 declarations; all `[propext]` |
| `AspisV8R19/R724BlockOrderChunk03.lean` | `e5d16510dbb41b7b4dcc81c714b214984c0972218f5a3fee8d1da24ebbe66da8` | `ae1563fcfa831567550e9f3fe8f69d357e16631c` | 0 | 0:01.76 | 490556 | 0 | 128 declarations; all `[propext]` |
| `AspisV8R19/R724BlockOrderChunk04.lean` | `558fb16e19c3bd43da489facb732a605fa4de97b144a9469958ed968c17b7936` | `ae1563fcfa831567550e9f3fe8f69d357e16631c` | 0 | 0:02.08 | 490704 | 0 | 128 declarations; all `[propext]` |
| `AspisV8R19/R724BlockOrderChunk05.lean` | `935e1bac5d8b3535f61958494d16f048c33526092c3900a5215e15fbbda5aea3` | `ae1563fcfa831567550e9f3fe8f69d357e16631c` | 0 | 0:02.33 | 491060 | 0 | 128 declarations; all `[propext]` |
| `AspisV8R19/R724BlockOrderChunk06.lean` | `c95a51849abed52c728f2774bd03e674a1754d1d6f34d3cb7b7c5755e5634346` | `ae1563fcfa831567550e9f3fe8f69d357e16631c` | 0 | 0:02.25 | 490992 | 0 | 120 declarations; all `[propext]` |
| `AspisV8R19/R766RowLeftTest.lean` | `fc2b6dcdc18a1d0a143331e93359a9eebfdb346271be9150f0cc192b3ad1e0e3` | `0b9748d4505885d3b72b36174d56dd5dea076383` | 0 | 0:01.83 | 1996852 | 0 | row_left: `[propext, Classical.choice, Quot.sound]` |
| `AspisV8R19/R766BlockOrderEquivalences.lean` | `042115f7b61271fc88f1285d162638f674efaa1b7295b2ebac638db0988e86f4` | `0b9748d4505885d3b72b36174d56dd5dea076383` | 0 | 0:06.43 | 2143196 | 0 | 6 declarations; all `[propext, Classical.choice, Quot.sound]` |

## Preserved failed consumer attempts

- `AspisV8R19/R766BlockOrderEquivalences.lean` source `d4906fe3d2c1d58af62a697db7657db9c0fa69c5b3231d397d635323aca9f67c`, rev `692d58235384abe81be54d7dba9c0b84574bd7bd`, exit 1, wall 0:00.18, RSS 471136 KiB, swap 0: Initial consumer lacked the `fin_cases` and Equiv imports; tactic and Equiv syntax errors.
- `AspisV8R19/R766BlockOrderEquivalences.lean` source `c98689de1b38e1cd821b114d51e6606fd7faf6a0b1b86f1595d524417264e91f`, rev `692d58235384abe81be54d7dba9c0b84574bd7bd`, exit 1, wall 0:00.60, RSS 1500492 KiB, swap 0: Added `FinCases` and Equiv imports; `FinCases` required a `Fintype (Fin 222)` instance.
- `AspisV8R19/R766BlockOrderEquivalences.lean` source `1d31f3f95266442f35c7e954dec44c49ebe558c1407be2dcb81bdd256e5630a8`, rev `0d5520c4197fcede4ec8e02d24ff0d40d75ba5fc`, exit 1, wall 0:48.09, RSS 2469072 KiB, swap 0: Added cached `Mathlib.Data.Fintype.Fin`; the all-facts-per-goal simp set failed to match constructor goals and emitted many unused-simp warnings.

## Pinned compilation environment

- Lean 4.32.0, compiler commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, binary and imported Mathlib source/olean SHA256 values are in `tool-and-cache-pins.json`.
- Focused targets ran through `run_focus.py` with `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Each receipt records its exact source revision and hash, target, runner hash, wall time, GNU-time child RSS, swap, and complete axiom print output.
- Successful outputs are `definitions`, `Case0`, Chunks00–06, the isolated row-left generic test, and the full R766 consumer. The consumer uses explicit `fin_cases` branches with exactly one matching named scalar fact in each branch; no matrix operations or elimination are present.

## Evidence organization

`successful/<run-id>/` and `failed/<run-id>/` each preserve `source.lean`, `log.txt`, and `receipt.json`. `sources/`, `generators/`, and `inputs/` preserve the generated map sources, first generic test, final consumer, Python generators, and pinned inventory/certificate/raw-matrix inputs. `manifest.json` hashes every bundled file.
