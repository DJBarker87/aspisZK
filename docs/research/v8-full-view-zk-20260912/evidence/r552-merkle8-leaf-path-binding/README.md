# R552 leaf-to-root eight-way binding — scratch evidence

Final target: `AspisV8R19/R552Merkle8LeafPathBinding.lean`. Final focused run
`1791073342628153000` exited 0 in 0.66 s; peak Lean-child RSS was 1,491,776
KiB and swap was 0. It used the pinned 5G/7G/swap0/tasks128 cgroup and
`-j1 -M4500`. All eight final `#print axioms` reports are standard only:
`propext`, `Classical.choice` where the inherited collision witness requires
it, and `Quot.sound`; no `sorryAx` occurs.

The result uses the literal `0x10, tag, packed ++ salt` leaf grammar. It
proves fixed-width packed-and-salt equality from equal same-tag literal inputs,
retains tags `0x71`/`0xf1`, and records C1 width 403, C2 width 186, and salt
width 32. It then splits on equality of the two **leaf hashes**: equal hashes
with unequal preimages yield a leaf collision; unequal leaf hashes feed the
entire R549 eight-way path theorem. The result is either equal packed/salt
records or an explicit collision from the full leaf-plus-six-parent traces.

The R549 dependency is the published canonical source SHA
`bde7ec439977c78be1d27ac1b02d41a53cc96c70d997786fc480c3d470f03910`;
Domains source SHA is `70c4b5e01f1644f2a7aa994f9ae3cba27a3fceb4bb998ec1ae43977cf98f1198`.
The cache lacked `Domains.olean`, so the focused dependency check
`1791073316009195000` is preserved. No source parser injectivity, native
frontier/path execution, graph completeness, probability, or security claim
is made.

Attempt `1791073309706295000` records the missing cached Domains object;
`1791073321744409000` records the initial theorem argument error. Their exact
sources, logs, and receipts are retained unchanged.
