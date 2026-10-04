# R691: exact circle coset roots

Verified mathematical target: `AspisV8R19/R691CircleCosetRoots.lean`.
Source revision: `d8e684eea7fdcc4b8dd7fd45db08f5ee092edd2b`.
Source SHA256: `7d790339f9246ca5b7dcc4b775a7bb38a57e49bd09f2a8bf054edb54e2c86a33`.

The exact generator literal certified by R690 has order 2^31. For each n < 2^18,
the first coordinate of g^(2^11 + 2^13*n) is distinct from every other such
coordinate and is never one. Equal first coordinates on the norm-one circle
mean identical points or inverse points; R689 excludes opposite exponents.
Squaring a norm-one point has first coordinate 2*x^2-1.

This proves the mathematical coset property without a probability loss. It does
not yet identify the actual selected fast table, bit reversal, field execution,
and returned query points with these powers. It is not an actual query execution
or end-to-end privacy/security theorem. The source-derived exponent route is
saved as an inventory, not assumed as an execution theorem.

Final focused run `1791124193496686000`: exit 0, wall 1.61s, Lean-child peak
RSS 3,272,360 KiB, swap 0. Pinned Lean 4.32, -j1 -M4500; systemd MemoryHigh5G,
MemoryMax7G, MemorySwapMax0, TasksMax128. The complete five #print axioms
reports are saved in the final log and release.json. All contain only subsets
of propext, Classical.choice, Quot.sound; no sorryAx/custom semantic axioms.

All six R691 attempts are retained, including the missing-import artifact and
unknown helper-name failures. R689's unchanged compiled artifact was copied
from its scratch output to the canonical import path; the successful dependent
compilation accepted it. Exact source/object checksums are in release.json.
No unchanged successful check or CU benchmark was rerun.

First remaining proposition: the actual selected three-window table and
18-bit reversal return the generator powers whose squared first coordinates
are these coset roots, preserving all source bounds and errors. The universal
legal C1/H1 compatibility, causal simulator and soundness obligations remain
open. CU 999,790 / 999,532 and security parameters remain unchanged.
