# L143 source enumeration

`FJi_Accumulations.enumeration` checks the exact source-ordered suffix of
`FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body`.
Named coordinates 0..7 select `c0.c0.a`, `c0.c0.b`, `c0.c1.a`, `c0.c1.b`,
`c1.c0.a`, `c1.c0.b`, `c1.c1.a`, `c1.c1.b` from the SAME `g[term]`.
Each extends that U32 and the SAME scalar to U64, multiplies, reads its old
sum, adds, and writes exactly that coordinate. Groups cover
[start,min(start+4,26)), starts 0,4,8,12,16,20,24. The byte scalar is decoded
from q[slot*120+term*4 .. +4]. Final group width is two.
Each group is folded `(s & 2147483647)+(s >> 31)` before its contribution
is added to the outer coordinate; after seven groups each coordinate is
canonicalized by `M31.reduce_u64`. Tail order is g[28] at slot*120+104,
g[26] at 480+slot*32, then g[27] at 496+slot*32, all QM31.

Attempt FJi_001: exit 0, wall 3.1477831370430067 s,
peak RSS 5446004 KiB, swap 0, axioms [propext, Classical.choice, Quot.sound].
Exact source revision/hash, dependencies, command and scope are in FJi_001/receipt.json.
This is enumeration only, not a loop value or L143 discharge.
Before/after top statements unchanged; native L143 and F3Y_G_L143 retained.
Recount delta 0T/0P/0G/0C. No new premise or shipped-file change.
