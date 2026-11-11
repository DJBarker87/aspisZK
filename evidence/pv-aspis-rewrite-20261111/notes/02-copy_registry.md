# 2. `build_pool_v1_pair_forest_copy_registry_v1`

File: `crates/aspis-statement/src/pool_v1/pair_forest_trace.rs` (module is
`#[cfg(not(target_os = "solana"))]`).

Old shape. For a scheduled link that is not a private-path link, the body looked
up the legacy link of the same kind with
`legacy.iter().find(|link| link.kind == scheduled.kind)` and returned `CopyLayout`
if there was none.

New shape. The lookup is the new private function `first_link_of_kind(&legacy,
kind)`, a counted `while` loop from index 0 that returns the first index whose
link has that kind, or `None`. The body takes `&legacy[index]`, or returns
`CopyLayout` when the result is `None`. Nothing else in the body changed; the
`map_err` closure on the schedule builder and the `for scheduled in schedule` loop
are as they were.

Why the behaviour is the same. `find` returns a reference to the first element,
in index order, for which the closure is true; the loop returns the index of the
first element for which the same comparison (`==` of the derived `PartialEq` on
the link kind) is true. `&legacy[index]` with that index is the same reference,
and the index is below `legacy.len()`, so the indexing cannot panic. The
comparison has no effect, so the number of comparisons made is not observable.
The error value and its place in the order of checks are unchanged. The output
vector is built by the same pushes in the same order.

Tests added (`pv_aspis_rw_copy_registry_matches_pin_body`): the function equals
the pin body on the two real builders (the function has no input of its own); the
helper equals `iter().position` and `iter().find` for every kind of the schedule
on the real legacy registry and on shortened, reversed and doubled copies, so
absent and repeated kinds both occur.
