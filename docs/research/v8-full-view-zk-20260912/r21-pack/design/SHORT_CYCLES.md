# Same support is not the same correction cost

The retained source completion chooses missing low coordinates in ascending
order for the external holes. Reconstructing that exact completion gives:

| Construction | Nontrivial cycles | Cycle lengths | Rank(P-I) |
| --- | ---: | --- | ---: |
| Current T163 permutation | 10 | one 145-cycle, nine 2-cycles | 153 |
| Close each forced path individually | 74 | 61 two-, 11 three-, two four-cycles | 89 |

Both move the identical 163 coordinates. Both retain the exact first 89 pad
images and the balancing pivot 1023. The inactive-sum row of T is unchanged.
These rank counts concern the PERMUTATION correction, not the full balanced
transform minus identity and not either cryptographic observation matrix.

## Construction and minimality

Let p[j] be the mandated pad image for 0 <= j < 89. The inspected p[j] is
strictly greater than j. Therefore the 89 mandated directed edges form a
forest of directed paths, not cycles. There are 74 initial vertices missing
from the image of these edges; each path ends at a vertex >= 89.

Keep p[j] for j<89. For each initial vertex, follow its path to its external
terminal, and map that terminal directly back to the initial vertex. Leave
all other vertices fixed. This closes 74 disjoint cycles and moves exactly
163 vertices.

For any permutation over any field, the kernel of P-I consists of vectors
constant on its cycles. Hence the correction rank is the sum of (length-1)
over nontrivial cycles. The new rank is 163-74=89.

The 89 fixed rows e_(p[j])-e_j are independent: they are oriented incidence
rows of a forest. Thus every linear completion satisfying these particular
fixed rows has correction rank at least 89. The constructed permutation
achieves that lower bound, as well as minimum support. No characteristic
exception is needed for the incidence-rank argument.

## Scalar correction formula

Use indexing `(Pw)[j]=w[p[j]]`. For one cycle c[0],...,c[k-1],

    sum_j (w[p[j]]-w[j])*v[j]
      = sum_(r=1..k-1) (w[c[r]]-w[c[0]])*(v[c[r-1]]-v[c[r]]).

This is k-1 bilinear products and additions. For a transposition it is one
product of differences. `generate_cycles.py` expands the complete formula
and compares every coefficient against the original matrix OVER THE INTEGERS.
It checks both the current map and the proposed map, not just random inputs.

This formula applies to the permutation term only. The inactive subtraction,
pivot, chord boundary/image terms and final relation must still be present.
It does not make the cost of forming w or v disappear. Nor does it justify
comparing 89 scalar products with an unrelated four-output source pipeline.
A caller-level SBF comparison is mandatory.

## Executed local checks

The new transport passes all 1024 coordinate-basis inverse/dual checks, all
89 balanced-pad images, and 128 arbitrary full-QM31 scalar correction checks.
The independent retained R18-style compatible-image model gives H1 rank 540
and G rank 601 at seeds 1 and 2 over M31, and separately at seeds 1 and 2 over
QM31. The latter use genuine four-limb challenge values.

These four parameter configurations are a small screening test. They do not
instantiate the actual q22 schedule, the full R19 p0/p2 observation system,
C1/H1/G affine witness target, seeded distribution or adaptive publication
law. No source-valid privacy conclusion follows. Before any integration,
repeat the *actual* 626-equation R19 correction checks and arbitrary-input
terminal differentials under a distinct profile identifier.

## Model provenance

`tests/model_cycles.hpp` is the independent R18 model retained in the user's
R19 packet. Its only constructor extension is `reset==3`, implementing the
path-closing map above. Existing reset 2 is the current T163 model. Field,
chord, circle, H1 and G matrix definitions are retained. This is explicitly
not Rust extraction. The input baseline ORDER is retained separately so an
actual-stage table can be compared before using generated constants.
