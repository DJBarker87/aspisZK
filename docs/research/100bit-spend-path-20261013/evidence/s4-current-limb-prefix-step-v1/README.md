# S4 actual inner-limb prefix step (focused v1)

The theorem `inner_body_success_advances_bound` composes the green actual
generated inner-limb-body arithmetic result with pointwise array update
readback. Given an input array whose eight entries are each at most `3 * cap`,
canonical scalar/coefficient bounds, and successful execution of the actual
inner body, it proves every output entry is at most `4 * cap`. The body result
is tied to its real `Array.update` writeback and the actual selected limb.

The included NUC preflight/receipt records source and direct-import object
hashes. The attempt passed fresh admission with 40.375 GiB finite reservations,
9.083 GiB uncapped working-set accounting, and an 8 GiB OS reserve. It ran
Lean 4.32.0 with `-j1 -M 4400` in a 1 GiB high / 2 GiB max / zero-swap scope:
exit 0, wall 1.405 seconds, process RSS 2,394,540 KiB, scope peak 298,225,664
bytes, scope swap 0. Both audited declarations depend only on
`[propext, Classical.choice, Quot.sound]`. No compiled objects are included.

The direct actual-body arithmetic dependency is
`FourDotsActualLimbArithmeticStepV2` (source SHA
`0118b360b80b48be250fe266b5791090d46f6675d23bff216d21d1198dc786b7`, object
SHA `726f43c01f148df45217595d285ddd7e842bdb46efbc34b7cb1e3fea6ce5360f`),
whose source snapshot is copied under `sources/dependencies/` and also appears
in `s4-current-arithmetic-closure-v1`. Aeneas Array and Lean Omega direct
imports are pinned in `attempt/preflight.json`.

This result is one step only. It does not prove that a limb loop visits each
index once, that the old-array `3 * cap` bound holds at every actual callback,
or that a complete four-term batch yields the required final accumulator
bound. Those loop-invariant and reducer connections remain open.
