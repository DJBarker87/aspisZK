# Exact identities behind the proposed optimizations

## A. The 1024-point cyclic power-sum algorithm

Let p=2^31-1, n=1024, a=1,...,271, and c_a be arbitrary QM31 coefficients. The source map is

    s_j = sum_a c_a a^j,  0 <= j < n.

All the following maps are linear over the extension field. Let

    S(X) = sum_{j=0}^{n-1} s_j X^j
    D(X) = product_a (1-aX)
    b_a = c_a (1-a^n)
    B(X) = sum_a b_a product_{t != a}(1-tX).

The current numerator tree computes exactly B when supplied b. At an nth root of unity w with w != 1, none of the factors 1-aw vanish for the fixed a. Therefore

    S(w) = sum_a c_a (1-(aw)^n)/(1-aw)
         = sum_a b_a/(1-aw)
         = B(w)/D(w).

The statement that none vanish is certified for the actual fixed nodes/root table by the supplied generators and tests. Equivalently a^n != 1 for a=2,...,271; a=1 is the unique exception. No challenge restriction is introduced.

At w=1, D(1)=0 and B(1)=0. Do NOT divide and do NOT put zero into S(1). Its correct value is

    S(1) = n*c_1 + sum_{a=2}^{271} c_a (1-a^n)/(1-a).

These are precomputable base-field coefficients. Compute this value directly from the original coins. Forward-transform the scaled numerator with n points, fill the nonsingular spectral coordinates by fixed inverse-D multiplication, overwrite coordinate zero by S(1), then inverse-transform.

There are n distinct roots and deg S < n. Equality at all roots establishes equality of every coefficient, hence the original power-sum map, for all coins. The actual root is the square of the retained 2048-point root; the generator uses the same source CM31 generator (2,1268011823).

This is not merely truncating a circular convolution. The normalized coins remove the wrap term. The checker retains two negative controls: reducing the old convolution length without normalization, and ignoring the exceptional coordinate.

No new hiding assumption, challenge inversion or transcript change occurs. The fixed singular frequency is public and handled for every input. Old/new arithmetic must still be connected to the actual compiled Rust words and canonical serialization.

## B. Geometric carries as nested averages

For a nonnegative source index j, let k be its number of trailing one bits, and define r_t to be j with its lowest t bits cleared. The source edge loop is

    X_j(v) = sum_{t=1}^k v[r_t]/2^t + v[j+1]/2^k.

For k=0 this is simply v[j+1]. For k>0 it equals

    (v[r_1] + (v[r_2] + ... + (v[r_k] + v[j+1])/2 ...)/2)/2.

Start at v[j+1], then read r_k,...,r_1 and repeatedly add and halve. Expanding the nesting proves exact equality in the odd-characteristic field. The source's four-limb half is the componentwise field half, not integer truncation.

Both formulas read the same indices but in a different order. The application is to pure vector reads only. Grouped input index 64 is zero-extended; the intermediate chord vector length 513 must remain intact. The test exercises j=0,...,1024, including all carry boundaries.

In three source chord calls of lengths 513,512,512, the total k is 1,533. The old expression performs 3,070 QM31 scalar products (each four M31 multiplies), plus 1,533 M31 scale updates: 13,813 M31 multiplies. The replacement uses 1,533 QM31 halves and additions. Compiler/runtime savings must be measured.

## C. The special pivot contribution

In Kernel::coordinate(1023), group = 63, local slot = 15. The local carry array has only slots 0,1,2. All carry inputs are therefore zero. Only normal input group 63 survives; it contributes to output 63>>4 = 3 with high index 63&15 = 15. The kernel's final eight halvings give

    [0, 0, 0, normal[15] * high[15] / 256].

This replaces one complete 64-group traversal without changing any other coordinate, quotient channel or image residual. The 80 independent grouped-model tests exercise this specialization.
