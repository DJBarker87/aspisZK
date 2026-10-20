# Current powers value mapped to EbyK push limbs (focused proof)

This focused Lean owner proves that a successful `weights.powers` callback, given canonical current power/state values, returns its prior value and that all eight coordinates of the corresponding EbyK `PushWide` are at most `2^31 - 2`. Its totality corollary derives the callback success from the retained concrete current `WideExact.mul` implementation and its source-graph theorem; callers do not supply a callback-success witness.

The packet pins the current multiplication source graph (`CurrentWideMulSourceGraph`, object SHA `1941b833e5407340bd6396324946d40dd4fc98009c8898a5eb8316d70cf1e51e`) and current powers callback owner through the recorded preflight. The proof uses explicit nested-coordinate maps between the callback representation and EbyK's `PushWide`.

Scope remains local to one callback. It does not yet prove that every value passed by the full `core::array::from_fn` powers-array caller is the callback result at the corresponding EbyK `Dot.push`, nor does it close the Rust array traversal or global R22 range argument. Those source/caller links remain open.

The admitted proof run exited 0 in 2.309 seconds, with process peak RSS 3,686,664 KiB, cgroup peak 361,373,696 bytes, and swap peak 0. The four printed theorem audits use only `[propext, Classical.choice, Quot.sound]`.
