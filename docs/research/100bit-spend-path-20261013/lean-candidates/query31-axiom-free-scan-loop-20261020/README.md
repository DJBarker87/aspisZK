# Query31 axiom-free scan/list-loop proof packet

This packet freezes focused checked sources and receipts for the Query31 scanner first-stop, concrete scan-step, list-loop, and array-order/list model. It intentionally contains no `.olean`/`.ir` files. Historical packets importing `TypesExternal` or `FunsExternal` are excluded from the accepted dependency chain.

## Checked results

- `Query31ScanTypesOnly`, `Query31ExplicitScanBody`, and `Query31UnrolledDriverFirstStop` are checked from the axiom-free owner. The first-stop result includes successful-driver trace inversion and `finish_success_iff`.
- `Query31ExplicitScanConcreteSteps.fresh_from_bounds` connects the fresh transition to Q22, with iterator advancement still an explicit operation.
- `Query31ExplicitListLoop.scanListLoop_q22` proves the scan body over list recursion, including empty, accepted-count 22, draw-count 64, fresh, and duplicate cases.
- `Query31ArrayIteratorOrder.pullN_is_take_drop` and `array_scan_q22` establish that the list pull model follows array value order. This is a list-backed model, not a proof of the generated Rust `IntoIter` methods.

All checked theorems report only `[propext, Classical.choice, Quot.sound]`. Full attempt receipts, commands, preflights, logs, and timings are in `evidence/`. Runner used Lean 4.32 on the NUC with `MemoryHigh=1GiB`, `MemoryMax=2GiB`, swap disabled, and fresh admission per focused stage.

## Exact object pins

- `Query31ScanTypesOnly`: `48fdc27e38b03d81ac57f2ec728753741d70aeed02d169ec58e5a277004887cd`
- `Query31ExplicitScanBody`: `668e6b68878eb97ac26825a0f0db84d3788975e657dcfeec772da442ef63c03d`
- `Query31UnrolledDriverFirstStop`: `ac6fdea9b28394d17ca484af9c0beaf2dcfb885c4cf769ff0b21d3fb605261e3`
- `Query31ExplicitScanConcreteSteps`: `f0c883196a1024d68e6d9644bc42fc5d3dcb5998d03622ca77364077e73a538f`
- `Query31ExplicitListLoop`: `b88e3785f4152a2707548dce1ea979eef0ef10e5a8b610c06b4ff2bf7bebfb65`
- `Query31ArrayIteratorOrder`: `8767a6bc9d111b0ee6fae0d81173e12ec397faf616a8e6943631086dc25a9ba2`

## Remaining boundary

The generated QueryScan `scan_loop` still calls Aeneas `Array.into_iter` and `IntoIter.next`. The generated `FunsExternal` owner declares these as external operations; prior list definitions model their conventional order/behavior but are not accepted source proofs of Rust `core::array::IntoIter`. Closing this gap requires either a pinned/extracted Rust core implementation and a body-pinned adapter to the five explicit operation parameters, or a precisely scoped standard-library semantic assumption accepted by the release policy. No current theorem in this packet asserts that correspondence.

The portable source snapshot now includes the exact generated `Funs.lean` and `Types.lean` used by the source adapter checker, the raw `FunsExternal_Template.lean` and `TypesExternal.lean` for diagnostics, and the Rust source/candidate inputs. `evidence/check_source_cut.py` runs solely from packet-relative files and checks the complete first-stop copied driver/finish/constants by a single import-only substitution, the scan body’s explicit-operation cut, minimal types, raw external declarations, and pinned source-file hashes. The Q22 dependency source and historical compile lineage are in `source-snapshot/lean/AspisV8R19` and `evidence/q22-source-lineage.json`.

The rust-src snapshot and unsafe implementation boundary are documented in `source-snapshot/iterator-boundary.md`. This closes source identity and call-path inspection, but not the generated external method refinement described there.
