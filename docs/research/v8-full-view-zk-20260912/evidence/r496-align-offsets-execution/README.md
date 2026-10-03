# R496 captured `align_to_offsets` execution — compiled evidence

This directory records the compiled R496 helper result in the supplied Aeneas
bounded-slice representation. The native memory and whole-parser obligations
remain open; no end-to-end privacy or security claim is made.

## Pinned inputs

- `R489WordArithmetic.lean` is the existing arithmetic dependency, SHA-256
  `ac6766da5acfc45ac29bfe3c00d927a495b2104c08b87f745356de1f77da04d5`.
- `source-pins/r488-selected-offsets.json` associates the actual selected
  helper with source `Fun20`; `r490-manifest.json` records its full selected
  name `core::slice::[inherent impl]::align_to_offsets::<u8,u32>`.
- `source-pins/r488-capture-d-compiler-constants.json` pins the compiler
  globals `SIZE(u32)=4`, `ALIGN(u32)=4`, `SIZE(u8)=1`, and `ALIGN(u8)=1`.
- `tool-pins/` pins the R497 concrete matcher tool binary by SHA-256 and size.

The raw generated module hashes are Types
`8f00513bc8c6de02ef56f21212d452060770495b8a6bbfc3ca7e38f4321a16b4` and
Funs `890991732d5adfb78c16ca0bab54818369e55fe64cfacfffffb99649778f69b9`.
The focused import-adapted module hashes are Types
`2cbf141792ff32e831544f3de17f4b9f533afe5b073821de456922800dde5c6a` and
the current Funs `43f4c8653771edb08081c34516a42f5be0a3376a11c3d6440832ba6681438acc`.
`generated/focused-import-adapter.json` records that only the Aeneas imports
were replaced by supplied cached constituent imports, plus the R498
definitionally identical primitive-name compatibility import for Funs. Every
other generated Funs byte is unchanged.

## Existing focused records

`r498-usize-aliases/` contains the complete green R498 alias snapshot,
receipt, raw log, and four complete `#print axioms` outputs. It compiled with
exit 0, wall 0:01.00, peak RSS 2,525,632 KiB, and zero swaps. It supplies the
names `Aeneas.Std.Usize.div` and `.rem` as definitions of the existing
`UScalar` primitives; it does not prove the R496 helper.

`focus-attempts/` retains the earlier raw Types aggregate failure, the adapted
Types success, and the prior adapted Funs failure on absent cached `Usize.div`
and `Usize.rem` aliases. It also contains the later Funs success after the
R498 import: exit 0, wall 0:00.96, peak RSS 2,527,856 KiB, zero swaps. These
results remain part of the factual boundary.

## R496 final focused result

`r496-final/` preserves the first focused failure, the worker's first green
result, and the final lead target. The final target compiled successfully with
exit 0, wall 0:01.09, peak RSS 2,534,804 KiB, and zero swaps. Its six complete
`#print axioms` reports contain only `propext`, `Classical.choice`, and
`Quot.sound`.

The final theorem proves the generated helper returns `ok (q,r)` for every
supplied bounded `Slice U8`, with `q = len / 4`, `r = len % 4`,
`q * 4 + r = len`, and `r < 4`; it also proves no generated-helper error result
and derives those facts from an observed successful result. This boundary is
only the supplied Aeneas bounded-slice representation. Native `align_to`
prefix/words/suffix image, ordered fields, Vec length and canonical/error
behavior, and the caller frame remain open.

`r498-source-check/` separately preserves the R498 name/source check and its
tool and Aeneas-library hash pins. It documents the exact existing primitive
specializations used by the focused target; it does not enlarge the R496
native-execution boundary.
