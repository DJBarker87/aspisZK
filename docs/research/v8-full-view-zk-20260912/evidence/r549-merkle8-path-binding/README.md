# R549 eight-way Merkle path binding — scratch evidence

Final target: `AspisV8R19/R549Merkle8PathBinding.lean`. Final focused check
`1791073052744206000` exited 0 in 0.90 s, peak Lean-child RSS 1,487,988 KiB,
swap 0, with the pinned 5G/7G/swap0/tasks128 cgroup and `-j1 -M4500`.
Complete axiom output is in its raw log: the eight theorems use only standard
`propext`, `Classical.choice` where recursion witnesses require it, and
`Quot.sound`; no `sorryAx` occurs.

The generic model fixes `Byte = Fin 256`, `Digest = Fin 26 → Byte`, and a
literal child-major node preimage `0x18 :: 208 bytes`. It proves length 209,
injectivity, selected-slot insertion with all other supplied child positions
unchanged, and the full same-slot-sequence path collision reduction. A depth-6
specialization retains an arbitrary six-slot list. The collision-free corollary
is explicitly restricted to the two traces. This is no native execution,
frontier-parser, graph-completeness, probability, or security result.

Frozen-source boundary reference: copied `r102_tree.rs` SHA-256
`ef6b526848c8800083bae56b097b46cd8821b2298a02e72c8d83b89ac3e79ea8`.
Its `parent` at lines 8-12 fixes child count 8, byte 0 `0x18`, 209 bytes, and
ranges `1+26*i .. 27+26*i`; `verify_reference` handles the separate frontier
parser at lines 37-56. No theorem binds either source body to this model.

Failed initial focused attempts are retained verbatim in `evidence/attempts/`:
`1791072980490689000` (unavailable cache import), `1791072992361569000`
(initial elaboration), and `1791073018780870000` (literal-length/index proof).
The earlier green `1791073039111181000` is retained; final rerun only removed
its unused-variable warning.
