# Native-effect assessment

The source laws and native RunJoin composition are distinct obligations.
Nothing in this campaign installs a real allocator, filesystem, or execution
world instance.

`PathBuf::deref`, `Path::join`, `String::as_ref<Path>` and
`PathBuf::as_ref<Path>` only manipulate the path's string/byte representation.
The retained `std/src/path.rs` and Unix path source contain their bodies.
They perform no open/stat/read/write or filesystem lookup. These operations
are not deferred for OS effects.

`Vec::try_reserve_exact` is different: its *recoverable Result* can depend on
native allocator state, including allocation failure. The current Aeneas Vec
carrier stores contents/length, not a native allocation/capacity/world. Merely
returning `Ok(())` with the original logical contents would drop the recoverable
error branch, violate the full-Result requirement, and is not used here.
V183/op32 therefore needs a concrete allocation-effect interpretation at
pv-runjoin (or an extracted source law retaining the exact allocator primitive
and recoverable error semantics). This is a source/representation obstruction,
not a checked counterexample to an established theorem. V183 remains OPEN;
no successful source callback is published for it.

The runtime allocator's abort-on-OOM trust item must also remain visible for
infallible allocation APIs. No timing/cache/allocation side-channel premise
is discharged by proving string or vector contents equations.
