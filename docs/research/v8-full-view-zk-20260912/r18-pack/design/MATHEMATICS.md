# R18: remove the costly G map, not its security checks

Pinned review base: `6677d5f1310ff7373301fbd79f186278f772e68a`.
This document proposes a NEW research protocol profile. It is not a claim
that R17 proof bytes remain valid or that full privacy / 100-bit soundness
has been established.

## 1. The retained transform supplies cheap independent coordinates

The current source transform is invertible:

- c[j] = g[order[j]], j < 1023;
- c[1023] = sum of g over the fixed inactive set.

For a legal G mask that last coordinate is zero. All other 1023 coordinates
are free in the ideal uniform-mask model. This is a model statement about
the existing balance hyperplane; the real shared-seed/oracle distribution
still needs the existing source proof.

Use the fixed, injective selection

    S(i) = 128 + 3*i, 0 <= i < 271.

Its last entry is 938. It omits the balancing coordinate and all first 128
code coefficients. Define u[i] = c[S(i)] = g[order[S(i)]]. These are 271
reads, not 271 evaluations of a degree-1023 polynomial.

The remaining 752 nonpivot code coordinates, in increasing order, complete
an explicit bijection:

    legal G <-> (u[271], remainder[752]).

The inverse fills the same slots, sets c[1023]=0 and uses the RETAINED T^-1.
It preserves every degree of freedom. No additional random coins are added.

This is not the failed `first271` placement. It is in CODE coordinates, is
spaced, and does not occupy complete early four-coefficient blocks. Nevertheless
these distinctions are only motivation: the compatible-image tests, and
ultimately a universal source proof, are mandatory.

## 2. Keep the ten-round structured polynomial

Keep exactly R17's zero-boundary polynomials and carry recurrence. If a(z)
are the existing 271 linear coefficients of mask_eval at the terminal point,
then

    mask_eval(G,z) = sum_i a_i(z) c[S(i)].

In original rows its covector is the scatter to order[S(i)]. In code
coordinates its covector is simply the scatter to S(i). In particular

    T^(-transpose) * (T^transpose * S^transpose * a) = S^transpose * a.

This is the crucial cancellation. Applying the old permutation correction
to this G sparse term AGAIN would be an implementation bug.

At the initial mask claim, the structured sum equals u[0], as in R17. Later
zero-boundary coefficients remain the same 27-per-round layout. Eta stays
after the initial claim. No verifier challenge becomes a fixed base-field
value, and no round polynomial degree is reduced as a shortcut.

All selected slots exceed 2. Thus the sparse term's values at code coefficient
indices 0, 1 and 2 are zero. It adds no interpolant subtraction at the two
selected coefficient entries; the retained two ordinary MLE contributions
and inactive term still DO contribute and must be included.

## 3. Sparse terminal via the existing 16-by-64 grouped kernel

Let L be multiplication by the actual circle chord and F the four-fold dual
operator. The desired sparse terminal is F L^transpose S^transpose a. R17's
retained grouped kernel has a 16-entry normal vector, three carry entries,
and 16 high weights. Instead of generating 1024 G weights:

- scatter the 271 products a_i * normal[S(i) mod 16] into 64 group sums;
- also add a_i * carry[local] when local < 3;
- run the unchanged 64-group right contraction and eight halvings.

The implementation and its independent direct-adjoint check are included.
The direct reference constructs each of the four lifted terminal unit
vectors, multiplies it by the full natural-basis chord (including the high
output tail), and dots at the selected coordinates. It does not repeat the
same grouped algorithm as its reference.

For S(i)=128+3i there are 51 selected low carry positions. Main contraction
work, EXCLUDING geometry and constructing a(z), is:

- 271 normal products;
- 51 carry products;
- 64 high-group products;
- four final kappa products if scaling is delayed until the output.

So this part has 386 ordinary field products before the optional four scales,
not a 271-by-1024 expansion, a numerator tree, or an FFT. These are logical
operation counts, NOT measured SBF CU.

The pure-read carry uses nested halves. All 64 output groups and the zero
extension at group 64 remain. Source image residuals are not included in
this helper and must be added separately, exactly as before.

## 4. Share the common ordinary functional without collapsing channels

Write U = inactive + k*E0 + k^2*E1 + k^3*E2, and M = S^transpose*a in code
coordinates. Let A be the retained transported/chord/fold version of U,
and E the same version of the unscaled ordinary E0. Let H be the sparse
chord/fold term above. Then the G base functional is

    A - k*E + k*H.

For the two four-entry final vectors R and G, the base terminal is exactly

    dot(R+G, A) - k*dot(G,E) + k*dot(G,H).

Compute A once. Do not independently construct two copies of the common
ordinary point/inactive functional. This identity remains true for arbitrary
vectors, not just honestly generated witnesses.

Do NOT replace the two quotient channels with their sum: the G correction
still needs G separately. Preserve both Final256 arrays, component OOD
claims, four image residuals, 44 query powers, canonical parsing and all
relation checks. Add each channel's image and fresh-query contribution
separately. The fresh query covectors begin AFTER the first fold and must
never be sent through L, T, or alpha0.

The same common-functional sharing identity can also be applied to the old
Vandermonde profile, but the large old G map remains there; sparse placement
is the principal structural saving.

## 5. Exact model tests performed

`structural_probe.cpp` reproduces the pinned natural-basis multiplication,
quotient image parametrization q[1023]=0 and b*q[1022]=c*q[1021], all 256
first-fold coefficients, 88 four-slot raw values, two ordinary MLE claims,
the balance constraint, 271 proposed semantic coin coordinates, and all six
sent coefficients of the first degree-six relation polynomial.

It builds the 624-by-1022 matrix. The intended rank is 601: 22 raw/fold
compatibility relations and one first-relation/final compatibility relation.
The separately serialized structured G point is determined by the 271
coins; adding that row would not add an independent dimension.

These are source-shaped finite arithmetic experiments, not a Rust extraction
or a transcript sampled by the honest q22 source. Raw points are constructed
by explicit rational parametrization, not by replaying the source q22 sampler.
The base and extension field results are separately reported in evidence.

A full source adapter must run the same new map against ACTUAL accepted source
prefixes, including the coupled opposite-witness C1/H1/G residual target. It
must verify original equations and image inclusions, not merely repeat the
rank. Fixed ranks are NOT a full privacy theorem. The unchanged source
commitment, shared-oracle, rejection, retry/publication and Fiat-Shamir
obligations remain.

## 6. A tempting broader basis reset was tested and rejected

I also constructed pi0(j)=16*(j mod 64)+15-floor(j/64), a bit permutation
and complementation. Swapping positions 128 and 1023 places source row 13
at the balance coordinate. The first 89 source rows are legal mask rows;
point tensor evaluation stays a tensor plus only two coordinate corrections.
Both transform inverses and raw balanced-mask basis identities pass.

However its full H1 homogeneous matrix has rank 517, not the existing 540,
in the tested base-field cases. G rank alone still passes. This is a 23-
dimensional H1 coverage loss, NOT a proof of a concrete published attack.
It is enough to reject this as a drop-in repair. Do not install it merely
because it is fast, reversible, or raw-private. Keep the current T.


## 7. A smaller, separately gated T improvement survives the same tests

A second permutation keeps precisely the existing pad images at positions
0..88 and pivot 1023. Unlike the rejected bit-affine rearrangement, it does
not permute all remaining coordinates. Let A={0,...,88} and B={old_order[j]:
j<89}. Set new_order[j]=old_order[j] for j in A. On B\A, place the unused
members of A\B in increasing order. Fix every position outside A union B.

The concrete source pad inventory gives |A intersect B|=15, so this permutation
has 163 changed coordinates, versus 479 for the original stable partition.
Every forced entry on A differs from its index. Every entry in B\A must move
because its original value was already used by A. Therefore 163 is also the
MINIMUM possible changed-coordinate support under these exact first-89 pins.
This is a combinatorial support optimum, NOT a measured CU optimum.

The balance pivot stays 1023 and the inactive set does not change. Every
retained balanced legal pad direction still maps to the same first-89 unit
coefficient. Thus the existing raw-interpolation argument remains applicable
after the actual source correspondence is established. No new randomness or
new code dimension is introduced.

The full modeled H1 rank stays 540 and sparse-G rank stays 601 in tested base
and QM31 cases. This is stronger screening than the rejected bit-affine
candidate passed, but still not full-view privacy. C1 witness residuals,
source coverage/minor certificates and the full transcript need replay.

The implementation opportunity is to store only the 163 changed coefficients
and their public cycle map, then use the same weighted grouped contraction.
Do NOT materialize the entire 479 prefix merely because its maximum index is
478. Gather source weights once at changed indices; apply cycles via fixed
compact positions; contract the 163 weighted coordinates. The fixed inactive
and pivot corrections remain. Use independently derived dense references in
host tests, never as a second full production verification pass.

Stage these changes separately: first sparse G with the original T, then the
163-support T under another explicit research profile. That isolates a G
repair failure from a basis-change failure and preserves an easier rollback.
