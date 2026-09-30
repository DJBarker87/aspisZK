# V7 R30 frozen closure replay

The first driver attempt at `2d1646ee5` stopped before compiling any module:
Lean required an explicit source root for a source outside the backend cwd.
Exact failed target `V7CallerCurrentReleaseR26.TypesExternal`: exit 1,
0.39s, peak 803856KiB, swaps 0. Driver aggregate exit 1, 1.01s,
peak 804176KiB, swaps 0. Remote log retained at
`/home/dombarker/project-offloads/v7-r30-closure-20260930/replay-2d1646ee5.log`.

Replacement driver supplies the generated/proof/staged module root with `-R`,
asserts the actual cgroup limits, and records cgroup memory peak/events on exit.
No Lean proof changed, no cap was raised, and no memory failure occurred.

Focused replacement preflight (`2d1646ee5+driver-fix`):
`V7CallerCurrentReleaseR26.TypesExternal`, exit 0, 1.76s,
peak 2534600KiB, swaps 0. Aggregate exit 0, 2.47s, peak 2534600KiB.
Cgroup peak 380964864 bytes, swap current 0, all memory pressure/OOM events 0.
Actual limits: high 7516192768, max 8589934592, swap max 0 bytes.

Frozen manifest SHA256:
`756adb168b68fd25ae1ace739ace2ef30b80638cf71b2633d74de6d9f7782fca`.
Order SHA256:
`291eedb3eb801f74510ad509d3592ee0e682b190060cb7d3570e45f19da6c0ef`.
Driver SHA256:
`58ac8616229f4860a1c70f8e03fb8f67856d3f18354e47875c359655ab68b3ec`.
Manifest validation is green for 336 transitive source modules; staging checks
all 142 callback sources against the previously frozen aggregate.

Final replay results will be appended after completion.
