# R0 Rust implementation specification — S1

Source snapshot: `5ebb3a99e49bc61538ac5f527bdf7c3fbe654f5e` (`v8-reference`), 2026-10-09. This expands [PLAN.md](PLAN.md), “What the Rust implements”. Citations below refer to that snapshot, including imported `AspisFormal` definitions. Formulas describe the Lean objects; the wire format and labels are **proposals**, not existing Lean constants. No Lean/Rust change or bridge proof is part of S1.

**Two implementation boundaries need an explicit owner decision.** The plan calls the initial encoder “circle encoder ∘ R16 transport”, but the actual `exactInitialEncoder` takes natural-basis coefficients directly and never applies that transport. Both maps, including a generating rule for the transport matrix, are specified below. Also, `Duplex.Params` requires a bounded, injectively decodable encoding of *every* message; its current message type contains arbitrary-degree polynomials and full C2 words. A compact commitment-root encoding is not an instance of that interface as written. The proposed compact bytes below do not silently resolve either boundary.

Use `F = M31`, `K = QM31`, and `E = WideExact` in Rust. Lean's generic parameter named `K` in `R0/`, `SemView`, and `MaskView` is instantiated with **E**, not necessarily Rust's QM31. Indices and row numbers here are zero-based. Use `a[0..n]` for exactly `n` entries; all field equalities and divisions are in the indicated field.

## 1. Fields, limbs, and block samplers

Let `p = 2147483647 = 2^31−1`. The tower is

```text
F = Z/pZ
CM31 = F[i] / (i² + 1)
K = CM31[u] / (u² − (2+i))
E = K[v] / (v² − u).
```

Thus an E value with limbs `d[0..8]` denotes

```text
(d0 + d1*i) + (d2 + d3*i)*u
  + ((d4 + d5*i) + (d6 + d7*i)*u)*v.
```

The order is `(c0.c0.a, c0.c0.b, c0.c1.a, c0.c1.b, c1.c0.a, c1.c0.b, c1.c1.a, c1.c1.b)`. K uses the first four entries; its embedding into E sets limbs 4–7 to zero. F's embedding sets limbs 1–7 to zero. Every stored M31 limb is the canonical integer `0 ≤ d < p`. This is **positional base-p rank**, not casting an integer into a characteristic-p field. Sources: [V5ComponentCQM31TowerExact.lean:12–22](../../../AspisFormal/AspisFormal/V5ComponentCQM31TowerExact.lean#L12-L22), [V5ComponentCQM31TowerExact.lean:42–47](../../../AspisFormal/AspisFormal/V5ComponentCQM31TowerExact.lean#L42-L47), [WideTower.lean:13–14](../v8-wide-reference-20261005/lean/WideTower.lean#L13-L14), [WideTower.lean:62–76](../v8-wide-reference-20261005/lean/WideTower.lean#L62-L76), [C/ModuloField.lean:25–43](../v8-r0-close-20261007/lean/R0C/ModuloField.lean#L25-L43), [V19/SamplerFieldDecode.lean:10–13](../v8-full-view-zk-20260912/lean/AspisV8R19/SamplerFieldDecode.lean#L10-L13).

An implementation can use the same quadratic rule at each layer: for generator `g²=r`, `(a+bg)(c+dg)=(ac+rbd)+(ad+bc)g`, and `(a+bg)⁻¹=(a−bg)/(a²−rb²)` when nonzero. The three `r` values are `−1`, `2+i`, and `u`. Zero inversion in Lean is total (`0⁻¹=0`); Rust `try_inv` should return failure where an operational denominator is required to be nonzero. Do not substitute a nonzero challenge filter for a denominator check.

For a squeezed block `b[0..32]`, define the unsigned 256-bit integer

```text
B = Σ(k=0..31) b[k] * 256^k
Digit_j(n) = floor(n / p^j) mod p.
```

All 32 bytes participate, with byte 0 least significant. The samplers are:

| Sampler / rows | Integer operation | Result |
| --- | --- | --- |
| `qm31Sample`, semantic 0–24 | `n = B mod p^4` | K with limbs `Digit_0(n)..Digit_3(n)`; `semChal` embeds it in E |
| `circleSample0/1`, rows 25/26 | Same `qm31Sample` | Circle map below |
| `ordinary`, rows 28–30 | `n = B mod p^8` | E with limbs `Digit_0(n)..Digit_7(n)` |
| `gammaNZ`, row 27 | `n = (B mod (p^8−1)) + 1` | E with limbs `Digit_0(n)..Digit_7(n)`; necessarily nonzero |

There is one squeezed block per scalar/circle row: no per-limb rejection, retry loop, masking to 31 bits, or nonzero filter for semantic challenges, κ, τ, or α. In `gammaNZ`, the plus one is on the **integer rank before decoding**, not field addition after decoding. Sources: [C/ModuloField.lean:18–23](../v8-r0-close-20261007/lean/R0C/ModuloField.lean#L18-L23), [C/ModuloField.lean:52–81](../v8-r0-close-20261007/lean/R0C/ModuloField.lean#L52-L81), [P/SemD2.lean:179–206](../v8-r0-sem-proof-20261008/lean/R0P/SemD2.lean#L179-L206), [C/V3/DuplexQ.lean:35–37](../v8-r0-close-20261007/lean/R0C/V3/DuplexQ.lean#L35-L37), [P/MaskInstance.lean:41–47](../v8-r0-sem-proof-20261008/lean/R0P/MaskInstance.lean#L41-L47).

For circle row `j∈{0,1}`, sample `t∈K`. Test `t.im ≠ 0`, i.e. at least one of limbs 2,3 is nonzero. If false, replace **the parameter** by `t0=u=(0,0,1,0)` at row 25 or `t1=1+u=(1,0,1,0)` at row 26. Then set

```text
x = (1 − t²)/(1 + t²)
y = 2t/(1 + t²)
z_j = (embed_K_to_E(x), embed_K_to_E(y)).
```

The fallbacks `(0,1)` and `(1,1)` are pairs of CM31 coordinates of a QM31 parameter, not circle `(x,y)` coordinates. The denominator is nonzero for the selected parameters. The output is non-base-rational. The combined parser rejects `z0=z1`; the sampler does not resample on equality. Sources: [P/CircleSampler.lean:26–33](../v8-r0-sem-proof-20261008/lean/R0P/CircleSampler.lean#L26-L33), [P/CircleSampler.lean:129–145](../v8-r0-sem-proof-20261008/lean/R0P/CircleSampler.lean#L129-L145), [P/CircleSampler.lean:175–189](../v8-r0-sem-proof-20261008/lean/R0P/CircleSampler.lean#L175-L189), [V19/SamplerCirclePolicy.lean:18–23](../v8-full-view-zk-20260912/lean/AspisV8R19/SamplerCirclePolicy.lean#L18-L23), [V15/CircleChord.lean:11–12](../v8-full-view-zk-20260912/lean/AspisV8R15/CircleChord.lean#L11-L12), [P/MaskView.lean:180–192](../v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean#L180-L192).

## 2. Duplex transitions and Q22, including its returned state

For a row with input state `s`, row label `l`, and encoded message `m`, the SHA-256 implementation proposed here performs

```text
s_abs = H(s || 0x00 || l || enc(m))
b     = H(s_abs || 0x01)
x     = H(s_abs || 0x02)
return (sample(b), x).
```

Both `b` and `x` use **s_abs**, not `b`. `H` is abstract in Lean; SHA-256 is the implementation choice from PLAN. The model's `Addr` padding is proof bookkeeping and is not hashed. Sources: [V19/DuplexFrames.lean:8–13](../v8-full-view-zk-20260912/lean/AspisV8R19/DuplexFrames.lean#L8-L13), [V19/SourceDuplexStep.lean:11–16](../v8-full-view-zk-20260912/lean/AspisV8R19/SourceDuplexStep.lean#L11-L16), [FS2/Duplex.lean:34–45](../v8-fs-generic-20261006/lean/FS2/Duplex.lean#L34-L45), [FS2/Duplex.lean:135–146](../v8-fs-generic-20261006/lean/FS2/Duplex.lean#L135-L146).

Row 31 first absorbs the final message once. Set `s[0]=s_abs` and compute **all eight** pairs, in order:

```text
for k in 0..8:
    b[k]   = H(s[k] || 0x01)
    x[k]   = H(s[k] || 0x02)
    s[k+1] = x[k]
```

There are 16 pair reads plus the one absorb. `DQ.chainS` reaches working state `x[7]`, then returns `DQ.out4`, whose state is selected by `scanOut`, potentially an earlier `x[k]`. The next `stateOf` uses that **returned** state. Do not replace `scanOut`'s state with the final working state. Sources: [C/V3/DuplexQ.lean:41–58](../v8-r0-close-20261007/lean/R0C/V3/DuplexQ.lean#L41-L58), [P/MaskProtocol.lean:123–131](../v8-r0-sem-proof-20261008/lean/R0P/MaskProtocol.lean#L123-L131), [FS2/Duplex.lean:135–138](../v8-fs-generic-20261006/lean/FS2/Duplex.lean#L135-L138).

`words 18 b` contains eight candidates, in increasing word index:

```text
word_j = b[4j] + 256*b[4j+1] + 65536*b[4j+2] + 16777216*b[4j+3]
candidate_j = word_j & 0x3ffff                  // word_j mod 2^18
```

The scan state is `(accepted: ordered list, draws: integer)`, initially `([],0)`. Duplicates count as draws but are not appended. The exact scan, including the order of its stop test, is:

```text
scan(q, []): return (q, false)
scan(q, [candidate] ++ rest):
    if len(q.accepted) == 22 or q.draws == 64:
        return (q, true)
    if candidate not in q.accepted:
        q.accepted.push(candidate)
    q.draws += 1
    return scan(q, rest)

finish(q):
    if len(q.accepted) == 22: return Ok(q.accepted)
    else: return Error(len(q.accepted))

scanOut(n, q, bs, xs, current):
    if n == 0: return (finish(q), current)
    if bs is empty or xs is empty: return (finish(q), current)
    if q.draws >= 64: return (finish(q), current)
    (q_next, stopped) = scan(q, words18(bs[0]))
    if stopped: return (finish(q_next), xs[0])
    return scanOut(n-1, q_next, bs[1..], xs[1..], xs[0])
```

Invoke `scanOut(8,([],0),b,x,s_abs)`. This is the literal recursion in [C/V3/Q22Law.lean:22–30](../v8-r0-close-20261007/lean/R0C/V3/Q22Law.lean#L22-L30), [C/V3/Q22Law.lean:95](../v8-r0-close-20261007/lean/R0C/V3/Q22Law.lean#L95-L95); scan/finish are [V19/Q22WordScan.lean:8–21](../v8-full-view-zk-20260912/lean/AspisV8R19/Q22WordScan.lean#L8-L21), and word decoding is [V19/SamplerWords.lean:9–11](../v8-full-view-zk-20260912/lean/AspisV8R19/SamplerWords.lean#L9-L11), [V19/SamplerWords.lean:21–31](../v8-full-view-zk-20260912/lean/AspisV8R19/SamplerWords.lean#L21-L31).

The empty-list clause executes **before** checking completion. If the 22nd distinct candidate is the eighth word of block `k<7`, the scan returns `false`; the next block's first word detects completion without consuming a draw, and the returned state is `x[k+1]`. If completion occurs earlier in a block, the next word in that block detects it and the returned state is `x[k]`. At the end of block 7, finishing at draw 64 returns `x[7]`, with success iff 22 distinct candidates were found. This boundary behavior is also recorded by `scan_empty_does_not_detect` and `completion_detection_block`: [V19/Q22WordScan.lean:65–71](../v8-full-view-zk-20260912/lean/AspisV8R19/Q22WordScan.lean#L65-L71), [V19/Q22SamplerProgram.lean:83–89](../v8-full-view-zk-20260912/lean/AspisV8R19/Q22SamplerProgram.lean#L83-L89).

An `Ok` list becomes the finite set of its fibre indices; error becomes the empty set. The acceptance wrapper requires `|S|=22`. Sampling order is preserved inside `scan` but `V1` only uses the resulting set. Proposed proof-opening order is increasing numeric fibre index, specified later. Sources: [C/V3/Q22Law.lean:89–95](../v8-r0-close-20261007/lean/R0C/V3/Q22Law.lean#L89-L95), [P/SemDecision.lean:111–115](../v8-r0-sem-proof-20261008/lean/R0P/SemDecision.lean#L111-L115), [P/MaskView.lean:376–387](../v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean#L376-L387).

## 3. Initial code, natural basis, R16, and domain indexing

The exact message is an array `q[0..1024]`. Define polynomials and their evaluators by

```text
D_0(X) = X
D_(b+1)(X) = 2*D_b(X)^2 − 1
N_j(X) = product of D_b(X) over the set bits b of j; N_0(X)=1
p0_q(X) = Σ(k=0..511) q[2k]   * N_k(X)
p1_q(X) = Σ(k=0..511) q[2k+1] * N_k(X).
```

These are `initialP0`, `initialP1`, and `naturalCoefficientPolynomial`. `N_j` is the product of power-of-two Chebyshev factors, **not** the monomial `X^j` and not generally the single Chebyshev polynomial `T_j`. Both p0 and p1 have degree ≤511. Sources: [CircleNaturalBasisEval.lean:19–44](../../../AspisFormal/AspisFormal/CircleNaturalBasisEval.lean#L19-L44), [V5FriInitialCircleEncoderIdentity.lean:48–53](../../../AspisFormal/AspisFormal/V5FriInitialCircleEncoderIdentity.lean#L48-L53), [V5FriInitialCircleEncoderIdentity.lean:124–139](../../../AspisFormal/AspisFormal/V5FriInitialCircleEncoderIdentity.lean#L124-L139), [V5FriConcreteEncoderApplicability.lean:294–296](../../../AspisFormal/AspisFormal/V5FriConcreteEncoderApplicability.lean#L294-L296), [V5FriConcreteEncoderApplicability.lean:323–327](../../../AspisFormal/AspisFormal/V5FriConcreteEncoderApplicability.lean#L323-L327).

For a stored initial domain point `(X_i,Y_i)` defined below,

```text
Enc(q)[i] = p0_q(X_i) + Y_i*p1_q(X_i),   0 ≤ i < 2^20.
```

This is literally `Wide.InitialEncoder.exactInitialEncoder`: [Wide/InitialEncoder.lean:29–39](../v8-wide-reference-20261005/lean/Wide/InitialEncoder.lean#L29-L39). For an arbitrary out-of-domain circle point `z=(x,y)`, use the same formula `evalMessage(q,z)=p0_q(x)+y*p1_q(x)`: [R0/Chord.lean:34–35](../v8-wide-reference-20261005/lean/R0/Chord.lean#L34-L35).

The coefficient conversion needed for the chord implementation is explicitly generated by

```text
M_n[d,j] = coefficient of X^d in N_j(X),   0 ≤ d,j < n.
monomial_coefficients = M_n * natural_coefficients
natural_coefficients  = inverse(M_n) * monomial_coefficients.
```

Generate `D_b` by the recurrence above and multiply the selected factors. `M_n` is triangular with nonzero diagonal; `monomialToNatural` is its inverse. Use `n=512` for the two initial halves and `n=256` for final messages. Source: [CircleNaturalBasis.lean:41–68](../../../AspisFormal/AspisFormal/CircleNaturalBasis.lean#L41-L68).

### R16 transport: formula and its currently missing connection

R16's separate transport takes an inactive set `I`, a pivot `piv∈I`, and a permutation `π` from coefficient indices to original row indices. Its full 1024×1024 matrix is generated by

```text
T[j,r] = 1 if π(j)=piv and r∈I
         1 if π(j)≠piv and r=π(j)
         0 otherwise.

(T m)[j] = Σ(r∈I) m[r] if π(j)=piv, else m[π(j)]
(T⁻¹ c)[r] = c[π⁻¹(piv)] − Σ(k∈I\{piv}) c[π⁻¹(k)] if r=piv,
             c[π⁻¹(r)] otherwise.
```

Its inverse-dual weight transport is

```text
(T⁻ᵀ w)[j] = w[π(j)] − w[piv] if π(j)∈I\{piv}, else w[π(j)].
```

The associated balancing map sets `m[piv]=−Σ(k∈I\{piv})m[k]` and leaves other entries alone. Sources: [V16/BalancedTransport.lean:12–17](../v8-full-view-zk-20260912/lean/AspisV8R16/BalancedTransport.lean#L12-L17), [V16/BalancedTransport.lean:58–62](../v8-full-view-zk-20260912/lean/AspisV8R16/BalancedTransport.lean#L58-L62), [V16/TransportDual.lean:12–19](../v8-full-view-zk-20260912/lean/AspisV8R16/TransportDual.lean#L12-L19).

The plan's composition would be `Enc_T(m)=Enc(Tm)`. Its message weights would have to use `T⁻ᵀ`, and a folded message would be `foldMessage(α,Tm)`. **That is not the `Enc(q)` used by the cited R0/R0P definitions**, which apply `eqWeight` and `indicator` directly to the same array that `exactInitialEncoder` treats as natural coefficients. `SemView.openingStmt` and `SemD3Glue.witness_baseTyped` do not insert T: [P/SemView.lean:111–116](../v8-r0-sem-proof-20261008/lean/R0P/SemView.lean#L111-L116), [P/SemD3Glue.lean:45–69](../v8-r0-sem-proof-20261008/lean/R0P/SemD3Glue.lean#L45-L69). An implementer must not add T to just the encoder while leaving those weights unchanged.

Lean R16 leaves `π` and `piv` as parameters; R0 does not instantiate them. For locating the older research implementation only, `tools/r16_basis_transport.rs:10–12,43–63` in `v8-full-view-zk-20260912` uses pivot 1023, takes the first 89 inactive rows below the pivot that are legal in all 16 semantic columns and are not row 1014, appends the remaining non-pivot rows in increasing order, and then the pivot. That is an external generating rule, **not a Lean-pinned R0 constant**. The Lean-spec implementation in the remainder of this document uses `Enc(q)` directly; selection of a transported profile remains explicit.

### The stored domain and fibres

Circle multiplication in F is `(x,y)*(x',y')=(xx'−yy',xy'+yx')`. Set `g=(2,1268011823)`; its order is `2^31`. Let `rev18(u)=Σ(b=0..17) bit_b(u)*2^(17−b)`. For fibre `u<2^18`, put `r=rev18(u)`. The initial flat index is `i=4u+s` for slot `s∈{0,1,2,3}`. Define

| Slot s | Natural domain index n(i) | Circle point |
| --- | --- | --- |
| 0 | `2r` | `(x_u,y_u)` |
| 1 | `2^20−1−2r` | `(x_u,−y_u)` |
| 2 | `2^19+2r` | `(−x_u,−y_u)` |
| 3 | `2^19−1−2r` | `(−x_u,y_u)` |

```text
(X_i,Y_i) = g^[ 2^10 * (2*n(i)+1) ]
(x_u,y_u) = g^[ 1024 + 4096*rev18(u) ]
exactCircleX(u) = embed_F(x_u)
exactCircleY(u) = embed_F(y_u)
line_node(u) = X(g^[2048 + 8192*rev18(u)]) = 2*x_u²−1.
```

`parentIndex(i)=floor(i/4)`, `slotIndex(i)=i mod 4`; the four children are consecutive, not separated by strides of `2^18`. Sources: [CircleGroupOrder.lean:21–25](../../../AspisFormal/AspisFormal/CircleGroupOrder.lean#L21-L25), [CircleGroupOrder.lean:174–176](../../../AspisFormal/AspisFormal/CircleGroupOrder.lean#L174-L176), [V6EncoderDistance.lean:31–35](../../../AspisFormal/AspisFormal/V6EncoderDistance.lean#L31-L35), [V5ComponentCConcreteFoldLinearity.lean:205–211](../../../AspisFormal/AspisFormal/V5ComponentCConcreteFoldLinearity.lean#L205-L211), [V7ExactOneFoldDomains.lean:36–58](../../../AspisFormal/AspisFormal/V7ExactOneFoldDomains.lean#L36-L58), [V7ExactOneFoldDomains.lean:119–139](../../../AspisFormal/AspisFormal/V7ExactOneFoldDomains.lean#L119-L139), [V7ExactOneFoldDomains.lean:266–278](../../../AspisFormal/AspisFormal/V7ExactOneFoldDomains.lean#L266-L278), [V7ExactOneFoldDomains.lean:330–356](../../../AspisFormal/AspisFormal/V7ExactOneFoldDomains.lean#L330-L356), [Wide/FinalEncoder.lean:115–123](../v8-wide-reference-20261005/lean/Wide/FinalEncoder.lean#L115-L123).

## 4. Four-point transform, final code, and dual fold

For a word `f[0..2^20]`, gather `a_s=f[4u+s]` and use `x=exactCircleX(u)`, `y=exactCircleY(u)`. The local transform φ is

```text
φ0 = (a0+a1+a2+a3)/4
φ1 = (a0−a1−a2+a3)/(4*y)
φ2 = (a0+a1−a2−a3)/(4*x)
φ3 = (a0−a1+a2−a3)/(4*x*y)

foldWord(α,f)[u] = φ0 + α*φ1 + α²*φ2 + α³*φ3.
```

Both x and y are nonzero on these fibres. To invert φ, the four values from channels `h[0..4]` are

```text
[h0+y*h1+x*h2+x*y*h3,
 h0−y*h1+x*h2−x*y*h3,
 h0−y*h1−x*h2+x*y*h3,
 h0+y*h1−x*h2−x*y*h3].
```

These are expansions of `fibreTransform`/`radix4Decode` and `fibreEvaluate`/`radix4Evaluate`, with inverses `(2y)⁻¹,−(2y)⁻¹,(2x)⁻¹`. Sources: [R0/Fold.lean:18–19](../v8-wide-reference-20261005/lean/R0/Fold.lean#L18-L19), [R0/Fold.lean:55–72](../v8-wide-reference-20261005/lean/R0/Fold.lean#L55-L72), [V5FriConcreteEncoderCommutation.lean:60–64](../../../AspisFormal/AspisFormal/V5FriConcreteEncoderCommutation.lean#L60-L64), [V5FriConcreteEncoderCommutation.lean:158–166](../../../AspisFormal/AspisFormal/V5FriConcreteEncoderCommutation.lean#L158-L166), [V5ComponentCConcreteFoldLinearity.lean:168–171](../../../AspisFormal/AspisFormal/V5ComponentCConcreteFoldLinearity.lean#L168-L171).

For a message `q[0..1024]`, channels are the consecutive coefficient lanes `q_s[d]=q[4d+s]`. Therefore

```text
foldMessage(α,q)[d] = q[4d] + α*q[4d+1] + α²*q[4d+2] + α³*q[4d+3]
exactFinalEncoder(F)[u] = Σ(d=0..255) F[d] * N_d(line_node(u)).
```

`F[0..256]` consists of **natural-line-basis coefficients**, not 256 evaluations or 256 monomial coefficients. `foldWord(α,Enc(q))=exactFinalEncoder(foldMessage(α,q))`. Sources: [V5FriConcreteEncoderCommutation.lean:306–314](../../../AspisFormal/AspisFormal/V5FriConcreteEncoderCommutation.lean#L306-L314), [Wide/FinalEncoder.lean:22–29](../v8-wide-reference-20261005/lean/Wide/FinalEncoder.lean#L22-L29), [Wide/FinalEncoder.lean:61–72](../v8-wide-reference-20261005/lean/Wide/FinalEncoder.lean#L61-L72), [R0/Fold.lean:87–105](../v8-wide-reference-20261005/lean/R0/Fold.lean#L87-L105), [R0/RoundNormalization.lean:36–40](../v8-wide-reference-20261005/lean/R0/RoundNormalization.lean#L36-L40).

For a weight vector `w[0..1024]`, define `ρ=[0,3,2,1]`. The cited dual fold and quarter are exactly

```text
citedDualFold(α,w)[d] = Σ(t=0..3) w[4d+t] * α^ρ[t]
                      = w[4d] + α³*w[4d+1] + α²*w[4d+2] + α*w[4d+3]
quarter = inverse(4) = 536870912 in F, embedded in E.
```

There is no quarter inside `citedDualFold`. V2 multiplies its dot product by quarter. All powers are nonnegative, so this definition also handles `α=0`; do not implement the dual fold as negative powers of α. Source: [R0/RoundNormalization.lean:22–28](../v8-wide-reference-20261005/lean/R0/RoundNormalization.lean#L22-L28).

## 5. Chord, interpolation, image functionals, and quotient weights

Write the two circle points as `z0=(x0,y0)` and `z1=(x1,y1)`, with `z0≠z1` and both outside the F-rational circle. Set

```text
a = secantA = x0*y1 − x1*y0
b = secantB = y0 − y1
c = secantC = x1 − x0
L(z0,z1)[i] = a + b*X_i + c*Y_i.
```

Do not rescale `(a,b,c)` independently of the quotient and weights. `L` has no zero on the stored domain under those point conditions. Sources: [R0/ChordGeometry.lean:11–18](../v8-wide-reference-20261005/lean/R0/ChordGeometry.lean#L11-L18), [R0/ChordImage.lean:21–24](../v8-wide-reference-20261005/lean/R0/ChordImage.lean#L21-L24), [R0/Chord.lean:25–32](../v8-wide-reference-20261005/lean/R0/Chord.lean#L25-L32).

For endpoint claims `Y=[Y0,Y1]`, choose x if `x1≠x0`, otherwise y:

```text
axis(z) = z.x if x1 != x0 else z.y
delta = axis(z1) − axis(z0)
slope = (Y1−Y0)/delta

interpolationPair = (Y0−slope*x0 + slope*X, 0)  if x1!=x0
                    (Y0−slope*y0, slope)       otherwise.
```

`delta≠0`. `interpolant(z0,z1,Y)` is `liftLinear(interpolationPair)`. Since `N_0=1`, `N_1=X`, this is the explicit 1024-array with all entries zero except

```text
x branch: I[0]=Y0−slope*x0, I[2]=slope
 y branch: I[0]=Y0−slope*y0, I[1]=slope.
```

Sources: [R0/Chord.lean:37–63](../v8-wide-reference-20261005/lean/R0/Chord.lean#L37-L63), [R0/Chord.lean:65–71](../v8-wide-reference-20261005/lean/R0/Chord.lean#L65-L71), [R0/PolynomialPair.lean:46–58](../v8-wide-reference-20261005/lean/R0/PolynomialPair.lean#L46-L58). `evalMessage(I,z0)=Y0`, `evalMessage(I,z1)=Y1`.

For general polynomial pairs `(p,r)`, `liftLinear(p,r)` means: truncate both in the **monomial** basis to degrees 0–511, multiply each resulting coefficient vector by `M_512⁻¹`, and interleave the two natural coefficient vectors at even/odd positions. This computes the unique pair specified by Lean's noncomputable `lift`. Truncating natural coefficients instead would be a different map. Sources: [R0/PolynomialPair.lean:18–32](../v8-wide-reference-20261005/lean/R0/PolynomialPair.lean#L18-L32), [R0/PolynomialPair.lean:34–58](../v8-wide-reference-20261005/lean/R0/PolynomialPair.lean#L34-L58), [R0/PolynomialPair.lean:103–127](../v8-wide-reference-20261005/lean/R0/PolynomialPair.lean#L103-L127).

The multiplication map and its two image conditions are

```text
mulP0(a,b,c,p,r) = (a+bX)*p + c*(1−X²)*r
mulP1(a,b,c,p,r) = c*p + (a+bX)*r
chordMessage(a,b,c,q) = liftLinear(mulP0(a,b,c,p0_q,p1_q),
                                  mulP1(a,b,c,p0_q,p1_q))
e1(q)     = coefficient_511(p1_q)
e2(b,c,q) = b*coefficient_511(p0_q) − c*coefficient_510(p1_q).
```

`chordLinear` is this linear message map, including the specified truncation. On `e1(q)=e2(b,c,q)=0` the product remains in the exact code and no truncation is needed. Sources: [R0/ChordDegree.lean:11–23](../v8-wide-reference-20261005/lean/R0/ChordDegree.lean#L11-L23), [R0/ChordImage.lean:70–82](../v8-wide-reference-20261005/lean/R0/ChordImage.lean#L70-L82), [R0/ChordImage.lean:101–123](../v8-wide-reference-20261005/lean/R0/ChordImage.lean#L101-L123).

The following generates the **entire exact matrix**, including its behavior off that kernel. Let `M=M_512`, `S h[d]=h[d−1]` for `d>0` and `S h[0]=0`. For `e[k]=q[2k]`, `o[k]=q[2k+1]`, compute

```text
h0 = (a*Id + b*S)*M*e + c*(Id−S²)*M*o
h1 = c*M*e + (a*Id + b*S)*M*o
chordMessage(q)[2k]   = (M⁻¹*h0)[k]
chordMessage(q)[2k+1] = (M⁻¹*h1)[k].
```

All matrices in this display have width 512, so shifting out the top entries implements monomial truncation. Let `C[a,b,c]` be the resulting 1024×1024 matrix. Then

```text
quotientWeights(a,b,c,w)[j] = Σ(r=0..1023) w[r]*C[a,b,c][r,j]
                           = (transpose(C[a,b,c])*w)[j].
```

Equivalently, build column `j` by applying `chordMessage` to the coordinate unit vector `ε_j`, and dot it with w. The name “quotientWeights” is the transpose of **multiplication by L**, not a pointwise division of weights. Sources: [R0/ChordImage.lean:141–146](../v8-wide-reference-20261005/lean/R0/ChordImage.lean#L141-L146), [R0/LinearDual.lean:11–17](../v8-wide-reference-20261005/lean/R0/LinearDual.lean#L11-L17), with the multiplication/lift definitions immediately above.

For any linear functional f, `FunctionalWeights.row(f)[j]=f(ε_j)`. In terms of M, the two needed rows are therefore

```text
row(e1)[2k]   = 0                    row(e1)[2k+1]   = M[511,k]
row(e2)[2k]   = b*M[511,k]           row(e2)[2k+1]   = −c*M[510,k].
```

Sources: [R0/FunctionalWeights.lean:9–10](../v8-wide-reference-20261005/lean/R0/FunctionalWeights.lean#L9-L10), [R0/ChordImage.lean:70–79](../v8-wide-reference-20261005/lean/R0/ChordImage.lean#L70-L79), [R0/PolynomialPair.lean:76–87](../v8-wide-reference-20261005/lean/R0/PolynomialPair.lean#L76-L87).

## 6. The three point claims, inactive set, and batched weights

The opening data `D` contains 29 initial words W; circle points z0,z1; endpoint claims `Y[l][j]` of shape 29×2; three ten-coordinate points `p_j`; point claims `C[j][l]` of shape 3×29; and an inactive subset `I⊆{0,…,1023}`. These have distinct roles: the 87 multilinear point claims are not the 58 circle endpoint claims. Source: [R0/OpeningDefinitions.lean:21–28](../v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean#L21-L28).

For `r<1024`, define `bit_b(r)=floor(r/2^b) mod 2`, with **b=0 the least significant bit**:

```text
eqWeight(p)[r] = product(b=0..9) (1−p[b] if bit_b(r)=0 else p[b])
indicator(I)[r] = 1 if r∈I else 0
<q,w> = Σ(r=0..1023) q[r]*w[r].
```

Sources: [R0/OpeningDefinitions.lean:30–34](../v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean#L30-L34), [R0/RoundNormalization.lean:28](../v8-wide-reference-20261005/lean/R0/RoundNormalization.lean#L28-L28).

R0P's sumcheck coordinates `A[0..10]` are **MSB first**, with A[9] the low bit. It concretely instantiates the opening points as follows:

```text
carry(k) = product(t=0..k−1) A[9−t], with carry(0)=1
succ(A)[c] = A[c] + carry(9−c) − 2*A[c]*carry(9−c)
xor12(A)[c] = 1−A[c] if c=6 or c=7, else A[c]
p_0[b] = A[9−b]
p_1[b] = succ(A)[9−b]
p_2[b] = xor12(A)[9−b].
```

Here `A[j]` is the challenge from combined row `15+j`. Honest `C[j][l]=<eqWeight(p_j),t_l>`. Sources: [P/SemView.lean:36–56](../v8-r0-sem-proof-20261008/lean/R0P/SemView.lean#L36-L56), [P/MaskView.lean:180–189](../v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean#L180-L189), [Z/HonestView.lean:63–70](../v8-r0-zk-20261009/lean/R0Z/HonestView.lean#L63-L70).

`I` is abstract in `Opening.Data` and `R0FS.Stmt`, but **fixed in the R0P instance**:

```text
r∈I  iff ((copyActiveRowMasks[r/16] >> (r mod 16)) & 1) == 0.
```

The 64 literal words, in increasing index order, are:

```text
[6144,6144,6145,6145,6145,6145,6145,6145,
 6145,6145,6145,6145,6145,6145,6145,6145,
 6145,6145,6145,6145,6145,6145,6145,6145,
 6145,6144,4097,2048,6145,2049,2048,6145,
 2049,6145,6145,6145,6145,6145,6145,6145,
 6145,6145,6145,6145,6145,6145,6145,6145,
 6145,6145,6145,6145,6145,4097,6145,6145,
 4097,26214,26214,26214,26214,26214,26214,1749]
```

This is `copyInactiveRows`, not an independently chosen tail interval or all maskable rows. Sources: [P/CopyConstants.lean:30–31](../v8-r0-sem-proof-20261008/lean/R0P/CopyConstants.lean#L30-L31), [P/Copy.lean:239–245](../v8-r0-sem-proof-20261008/lean/R0P/Copy.lean#L239-L245), [P/SemView.lean:111–116](../v8-r0-sem-proof-20261008/lean/R0P/SemView.lean#L111-L116).

Set `I_l=interpolant(z0,z1,Y[l])` and define

```text
R_l[i] = (W_l[i] − Enc(I_l)[i]) / L[i]
R_γ[i] = Σ(l=0..28) γ^l * R_l[i]
t_γ[r] = Σ(l=0..28) γ^l * t_l[r]
I_γ[r] = Σ(l=0..28) γ^l * I_l[r]
v_honest = Σ(r∈I) t_γ[r].
```

The batch powers are exactly `γ^0,…,γ^28`. They are not the special mask-factor exponents from the semantic phase. The scalar v is the inactive sum of the **original batched message**, before chord subtraction/division. Sources: [R0/OpeningDefinitions.lean:36–51](../v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean#L36-L51), [V6Width29CorrelatedAgreement.lean:25–26](../../../AspisFormal/AspisFormal/V6Width29CorrelatedAgreement.lean#L25-L26), [V6Width29CorrelatedAgreement.lean:64–66](../../../AspisFormal/AspisFormal/V6Width29CorrelatedAgreement.lean#L64-L66), [Wide/EncoderLinearity.lean:152–167](../v8-wide-reference-20261005/lean/Wide/EncoderLinearity.lean#L152-L167), [Z/HonestView.lean:295–300](../v8-r0-zk-20261009/lean/R0Z/HonestView.lean#L295-L300).

The verifier computes these arrays/scalars entirely from the points and claims:

```text
weights[r] = κ*eqWeight(p_0)[r] + κ²*eqWeight(p_1)[r]
             + κ³*eqWeight(p_2)[r] + indicator(I)[r]
claim      = κ*Σ_l γ^l*C[0][l] + κ²*Σ_l γ^l*C[1][l]
             + κ³*Σ_l γ^l*C[2][l] + v
claimPrime = claim − <weights,I_γ>
qWeights   = quotientWeights(a,b,c,weights)
totalWeights[r] = qWeights[r] + τ*row(e1)[r] + τ²*row(e2(b,c))[r].
```

The inactive indicator's coefficient is 1, and κ powers start at 1. `imageFunctional(D,0)=e1`, `imageFunctional(D,1)=e2(b,c)`. Sources: [R0/OpeningDefinitions.lean:42–67](../v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean#L42-L67). In the same notation, `discrepancy[j][l]=C[j][l]−<eqWeight(p_j),t_l>`, `pointDefect[j]=Σ_l γ^l*discrepancy[j][l]`, and `inactiveDefect=v−<indicator(I),t_γ>`: [R0/OpeningDefinitions.lean:45–51](../v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean#L45-L51).

## 7. Honest quotient, round polynomial, and the six transmitted coefficients

For an honest committed message `t_l`, set `Y[l][0]=evalMessage(t_l,z0)` and `Y[l][1]=evalMessage(t_l,z1)`. Let `q_l` be the unique message with

```text
Enc(q_l) = (Enc(t_l) − Enc(interpolant(z0,z1,Y[l]))) / L.
q = Σ(l=0..28) γ^l*q_l
w = totalWeights(D,κ,τ).
```

This is the honest `quotientLinear` followed by `batchLinear`; `q` is the message of the batched **virtual quotient**, not `t_γ` or `t_γ−I_γ`. Lean defines the quotient decoder through a total linear left inverse; on distinct non-base circle points the quotient has a unique encoded preimage. Sources: [Z/HonestView.lean:148–165](../v8-r0-zk-20261009/lean/R0Z/HonestView.lean#L148-L165), [Z/QuotientImage.lean:69–75](../v8-r0-zk-20261009/lean/R0Z/QuotientImage.lean#L69-L75), [Z/QuotientImage.lean:124–145](../v8-r0-zk-20261009/lean/R0Z/QuotientImage.lean#L124-L145).

An explicit coefficient procedure is to solve for q_l in the message map from §5:

```text
C[a,b,c]*q_l = t_l−I_l,
e1(q_l)=0, e2(b,c,q_l)=0.
```

All entries of this linear system were generated above; it characterizes that unique honest preimage. This specifies the result without choosing a new off-image decoder or an FFT/inversion algorithm. The source's noncomputable extension off the encoded image is not a concrete Rust fallback policy.

The honest PCS polynomial is exactly `P_open(X)=roundPolynomial(q,w)`:

```text
P_open(X) = (1/4) * Σ(d=0..255) Σ(s=0..3) Σ(t=0..3)
                        q[4d+s]*w[4d+t]*X^(s+ρ[t]),  ρ=[0,3,2,1].
```

For each d, write `q_s=q[4d+s]`, `w_s=w[4d+s]`; each coefficient below is quarter times the sum of the displayed expression over all 256 d:

| Coefficient | Expression inside `¼ Σ_d` |
| --- | --- |
| c0 | `q0*w0` |
| c1 | `q1*w0 + q0*w3` |
| c2 | `q2*w0 + q1*w3 + q0*w2` |
| c3 | `q3*w0 + q2*w3 + q1*w2 + q0*w1` |
| c4 | `q3*w3 + q2*w2 + q1*w1` |
| c5 | `q3*w2 + q2*w1` |
| c6 | `q3*w1` |

Send **`[c0,c1,c2,c3,c5,c6]` in that order** in the proposed compact proof. Reconstruct `c4=quarter*claimPrime−c0`; coefficients above degree 6 are zero. The honest `c0+c4=quarter*<q,w>=quarter*claimPrime`, and after the row-30 challenge α the honest final message is `F=foldMessage(α,q)`. Sources: [R0/RoundNormalization.lean:22–40](../v8-wide-reference-20261005/lean/R0/RoundNormalization.lean#L22-L40), [R0/RoundNormalization.lean:43–71](../v8-wide-reference-20261005/lean/R0/RoundNormalization.lean#L43-L71), [Z/HonestView.lean:297–300](../v8-r0-zk-20261009/lean/R0Z/HonestView.lean#L297-L300). The omitted-coefficient format is a proposal from PLAN; Lean's `.poly` contains the entire polynomial.

## 8. V1, V2, Accept, and the enclosing verifier

The following is verbatim from [R0/OpeningDefinitions.lean:102–113](../v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean#L102-L113) (K here is instantiated as E):

```lean
def V1 (D : Data K) (gamma alpha : K) (F : FinalMessage K) (S : Finset (Fin 262144)) : Prop :=
  ∀ u ∈ S, exactFinalEncoder F u = foldWord alpha (batch D gamma) u

def V2 (D : Data K) (kappa tau alpha : K) (P : K[X]) (F : FinalMessage K) : Prop :=
  P.eval alpha = quarter*dot F (citedDualFold alpha (totalWeights D kappa tau))

/-- Semantic and authentication checks are abstract Boolean propositions here. -/
def Accept (D : Data K) (gamma v kappa tau alpha : K) (P : K[X])
    (F : FinalMessage K) (S : Finset (Fin 262144)) (semantic authentic : Prop) : Prop :=
  semantic ∧ authentic ∧ P.natDegree ≤ 6 ∧
  P.coeff 0+P.coeff 4 = quarter*claimPrime D gamma v kappa ∧
  V1 D gamma alpha F S ∧ V2 D kappa tau alpha P F
```

For V1, authenticate the 29 lanes at each of the four points `4u+s`, compute those four values of `R_γ`, apply φ and the α powers, and compare with `Σ_d F[d]*N_d(line_node(u))`. For V2, evaluate the degree-six polynomial at α and compare with `quarter*Σ_d F[d]*citedDualFold(α,totalWeights)[d]`. `F` must be fixed before S is sampled.

`Accept` itself does not contain `|S|=22`, nor does it require `γ≠0`. The sampler enforces nonzero γ and `decisionZ` adds `cardOK`. `R0FS.decision` requires the exact five-round list

```text
[(values Y,γ), (scalar v,κ), (unit,τ), (poly P_open,α), (final F,S)]
```

followed by `.opening`; its route-A authentication argument is literally `True` because W consists of complete abstract words. `openingViewZ` additionally checks the two circles and C2 field membership. Sources: [F/Protocol.lean:127–135](../v8-r0-fs-20261006/lean/R0FS/Protocol.lean#L127-L135), [P/MaskView.lean:180–192](../v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean#L180-L192), [P/MaskView.lean:376–387](../v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean#L376-L387). Rust must supply actual authentication rather than implement the `True` placeholder as a Merkle check.

The preserved semantic phase feeds its 87 claims to that view. Its masked sumcheck checks ten polynomials `h_j`, each degree ≤27:

```text
h_0(0)+h_0(1) = maskSum
h_(j+1)(0)+h_(j+1)(1) = h_j(A[j])             (j=0..8)
h_9(A[9]) = maskValueClaims(B,C[0],A)
            + η*terminalValue(pub,λ,χ,θ,μ,zc,B,C,A).
```

The honest row-14 claim is `maskTotal=Σ_{b∈{0,1}^10} maskValueClaims(B,honestClaims(t,b)[0],b)`; it is distinct from the PCS inactive sum v. `maskValueClaims` reads semantic lanes 0–15, mask-only lanes 16–25, and G at lane 27; lane 28 has zero mask factor. Sources: [P/MaskProtocol.lean:49–62](../v8-r0-sem-proof-20261008/lean/R0P/MaskProtocol.lean#L49-L62), [P/MaskProtocol.lean:93–102](../v8-r0-sem-proof-20261008/lean/R0P/MaskProtocol.lean#L93-L102), [P/MaskInstance.lean:11–15](../v8-r0-sem-proof-20261008/lean/R0P/MaskInstance.lean#L11-L15). This document specifies the retained semantic interface, not a replacement for the per-family semantic definitions.

## 9. Proposed proof encoding, p.enc, and row labels

**Proposal P1**, for owner review: a fresh `aspis:r0:20261009:v1` domain and no reuse of a v7 PCS proof tag. Use one-byte row labels `lbl(i)=0xa0+i` for `0≤i<32`. These labels are independent of message constructor tags. Every absorb data buffer is `tag:u8 || payload_length:u32_le || payload`, with exactly the prescribed payload size; no trailing bytes. Integers and field limbs are little-endian. Encode E as eight canonical `u32_le` limbs in §1 order (32 bytes), K as four (16 bytes), and F as one (4 bytes); field parsers reject limbs ≥p. Unless explicitly typed F/K below, arrays in the transcript proposal use E, including embedded semantic values. These byte choices are not fixed by Lean.

There are three layers which must not be conflated:

1. **Compact proof wire.** Sends roots in place of complete committed words and sends six PCS coefficients. It is the proposed Rust-facing format below.
2. **Decoded algebraic messages.** The six coefficients are expanded to a complete polynomial using `claimPrime`; the final openings are authenticated against roots. These are the values on which the formulas above operate.
3. **`p.enc`.** For scalar/array messages it is the canonical tagged encoding below. For `.poly`, propose that the transcript absorbs the **full reconstructed seven coefficients** `c0..c6`, even though only six were sent on the proof wire. Then the encoding of a degree≤6 polynomial is context-independent; only proof-wire decoding uses the preceding claims. Hashing just six coefficients cannot satisfy `decEnc` on unrestricted `.poly` values. For C2, the practical proposal hashes the root, and the corresponding whole-word `p.enc` interface remains a commitment-model boundary.

The complete proposed row schedule is below. `none` has empty payload/tag `00`; all polynomial arrays have increasing monomial degree order. `h_j` means a masked semantic sumcheck polynomial, not H1. “E sampler” means §1 `ordinary`; “K sampler” means `semChal`.

| Row | Label | Message absorbed before the challenge; payload order | Tag | Challenge |
| --- | --- | --- | --- | --- |
| 0 | `a0` | `semantic(base none)`; C1 already bound in initial state | `00` | λ, K sampler |
| 1 | `a1` | `semantic(base none)` | `00` | χ, K sampler |
| 2 | `a2` | `semantic(base(h1 H1 G))`; compact C2 root, lane order 26 then 27 | `01` | θ, K sampler |
| 3 | `a3` | `semantic(base none)` | `00` | zc[0], K sampler |
| 4 | `a4` | `semantic(base none)` | `00` | zc[1], K sampler |
| 5 | `a5` | `semantic(base none)` | `00` | zc[2], K sampler |
| 6 | `a6` | `semantic(base none)` | `00` | zc[3], K sampler |
| 7 | `a7` | `semantic(base none)` | `00` | zc[4], K sampler |
| 8 | `a8` | `semantic(base none)` | `00` | zc[5], K sampler |
| 9 | `a9` | `semantic(base none)` | `00` | zc[6], K sampler |
| 10 | `aa` | `semantic(base none)` | `00` | zc[7], K sampler |
| 11 | `ab` | `semantic(base none)` | `00` | zc[8], K sampler |
| 12 | `ac` | `semantic(base none)` | `00` | zc[9], K sampler |
| 13 | `ad` | `semantic(base none)` | `00` | μ, K sampler |
| 14 | `ae` | `semantic(maskSum m)`; one E | `03` | η, K sampler |
| 15 | `af` | `semantic(base(roundPoly h_0))`; 28 E, coefficients 0..27 | `02` | A[0], K sampler |
| 16 | `b0` | `semantic(base(roundPoly h_1))`; 28 E | `02` | A[1], K sampler |
| 17 | `b1` | `semantic(base(roundPoly h_2))`; 28 E | `02` | A[2], K sampler |
| 18 | `b2` | `semantic(base(roundPoly h_3))`; 28 E | `02` | A[3], K sampler |
| 19 | `b3` | `semantic(base(roundPoly h_4))`; 28 E | `02` | A[4], K sampler |
| 20 | `b4` | `semantic(base(roundPoly h_5))`; 28 E | `02` | A[5], K sampler |
| 21 | `b5` | `semantic(base(roundPoly h_6))`; 28 E | `02` | A[6], K sampler |
| 22 | `b6` | `semantic(base(roundPoly h_7))`; 28 E | `02` | A[7], K sampler |
| 23 | `b7` | `semantic(base(roundPoly h_8))`; 28 E | `02` | A[8], K sampler |
| 24 | `b8` | `semantic(base(roundPoly h_9))`; 28 E | `02` | A[9], K sampler |
| 25 | `b9` | `beforeZ0 C`; 87 E, outer point j=0..2 then lane l=0..28 | `04` | z0, `circleSample0` |
| 26 | `ba` | `beforeZ1 Y0`; 29 E, lane l=0..28 | `05` | z1, `circleSample1` |
| 27 | `bb` | `opening(values Y)`; 58 E, outer lane l=0..28 then endpoint j=0,1 | `06` | γ, `gammaNZ` |
| 28 | `bc` | `opening(scalar v)`; one E | `07` | κ, E sampler |
| 29 | `bd` | `opening unit`; empty payload | `08` | τ, E sampler |
| 30 | `be` | `opening(poly P_open)`; seven reconstructed E, c0..c6; wire carries six c0,c1,c2,c3,c5,c6 | `09` | α (PLAN's opening α₀), E sampler |
| 31 | `bf` | `opening(final F)`; 256 E, index d=0..255 | `0a` | S, full Q22 chain |

The table's algebraic constructors and timing are fixed by [P/MaskProtocol.lean:15–36](../v8-r0-sem-proof-20261008/lean/R0P/MaskProtocol.lean#L15-L36), [P/SemView.lean:30–34](../v8-r0-sem-proof-20261008/lean/R0P/SemView.lean#L30-L34), [C/SemStatement.lean:20–31](../v8-r0-close-20261007/lean/R0C/SemStatement.lean#L20-L31), [F/Protocol.lean:50–60](../v8-r0-fs-20261006/lean/R0FS/Protocol.lean#L50-L60), [F/Protocol.lean:130–135](../v8-r0-fs-20261006/lean/R0FS/Protocol.lean#L130-L135); sampler row assignments are [P/MaskInstance.lean:41–47](../v8-r0-sem-proof-20261008/lean/R0P/MaskInstance.lean#L41-L47). Labels, tags, byte sizes, padding and compact serialization are proposed here. There is no extra challenge after row 31. Final `.opening` has tag `0b` in a typed proof-record format, with authenticated opening bytes described below; it is **not an extra absorb/squeeze row**.

Before row 0, propose

```text
iv = SHA256(ASCII("aspis:r0:20261009:v1") || 0x00
            || u32_le(len(public_bytes)) || public_bytes || C1_root[32]).
```

`public_bytes` follows `R0P.Public` declaration order: variant (0=privateTransfer, 1=withdrawal), anchor[8], nullifier[8], assetId, recipient option, change[8], withdrawalAmount option, nextPairIndex, snapshotFrontier[20][8], nextRoot[8], nextFrontier[20][8]. Use canonical F limbs for each digest/scalar, `u8` option discriminants 0/1 followed by a payload only for 1, and `u64_le` for nextPairIndex. Reject an unrepresentable index. This is a proposed concrete subset/serialization of a structure whose `nextPairIndex` is an unbounded Nat and whose field/subfield parameters remain generic: [P/Core.lean:48–67](../v8-r0-sem-proof-20261008/lean/R0P/Core.lean#L48-L67), [P/SemView.lean:59–67](../v8-r0-sem-proof-20261008/lean/R0P/SemView.lean#L59-L67). `p.iv` itself is just an input state in [FS2/Duplex.lean:61–72](../v8-fs-generic-20261006/lean/FS2/Duplex.lean#L61-L72); statement hashing is not fixed there.

Commit C1 before λ/χ with lanes `[0,1,…,25,28]` in that order; commit C2 after λ/χ with lanes `[26,27]`. Proposed compact row-2 payload is one 32-byte C2 root. D is in the initial context, not a third adaptively chosen C2 lane. In the ideal model row 2 instead contains **both complete words** H1 and G. `c2Words` changes only lanes 26/27 of `TypedContext.W`: [P/SemView.lean:59–78](../v8-r0-sem-proof-20261008/lean/R0P/SemView.lean#L59-L78), [P/SemView.lean:90–94](../v8-r0-sem-proof-20261008/lean/R0P/SemView.lean#L90-L94). Field typing proposal is F for lanes 0–25 and K for 26–28, embedded in E. Lean only fixes the common subfield for lanes below 26, so the remaining field choices need a concrete instance.

Propose final openings sorted by ascending `u∈S`, then slot s=0..3, then lane l=0..28. Each value is encoded in its commitment field (F for 0–25, K for 26–28), for 88 initial positions and 2552 lane values. The verifier derives indices from S; the proof does not supply an alternative query list. Attach the C1/C2 eight-way authentication data in the selected existing R552 tree format, in the same order. This document fixes value ordering, but does **not** invent an R552 node/path serialization or claim it is present in `Msg.opening`, which has no payload in Lean. Authentication/root-format binding is an explicit remaining interface.

`beforeZ1 Y0` is absorbed before z1. The honest row-27 values repeat that Y0, but `openingViewZ` matches `.beforeZ1 _` and discards it; **it does not check that the repeated column equals the earlier payload**. For literal acceptance semantics retain both records and use row 27's 29×2 values; adding an equality guard would be a further verifier restriction, not a cited Lean check. Source: [P/MaskView.lean:182–189](../v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean#L182-L189).

### Limits of this p.enc proposal

`FS2.Duplex.Params` requires `encLen : ∀m, length(enc m)≤D` and `decEnc : ∀m, dec(enc m)=some m`: [FS2/Duplex.lean:61–72](../v8-fs-generic-20261006/lean/FS2/Duplex.lean#L61-L72). Consequently:

- A literal encoding of `.h1 H1 G` must preserve the complete two words (for example, lane-major, then i=0..2^20−1, each E). A 32-byte root cannot injectively encode that type. The compact row-2 proposal requires a commitment-aware message/refinement interface; it is not supplied by `SemD3Glue.openingParams` or `MaskProtocol.openingParamsAt`, which simply reuse `p.enc/p.dec`.
- The semantic and opening polynomial constructors contain arbitrary `E[X]`, an infinite type. No fixed finite D can support `encLen` plus `decEnc` for that entire current message type. The fixed arrays of 28 and 7 coefficients above give bounded encodings for **valid degree-bounded messages only**. Rejecting other wire inputs does not on its own instantiate the existing all-message Lean interface.
- Six wire coefficients can decode contextually into the seven-coefficient message, but six bytestring fields alone are not an injective `p.enc` for all polynomial messages. The proposed full reconstructed transcript encoding isolates that issue; the bounded message interface still has to be supplied.

These are source-interface findings, not proposed theorem premises. No bridge or restriction of the Lean types is made in S1. The wrapper encoders are [P/SemD3Glue.lean:532–548](../v8-r0-sem-proof-20261008/lean/R0P/SemD3Glue.lean#L532-L548), [P/MaskProtocol.lean:106–120](../v8-r0-sem-proof-20261008/lean/R0P/MaskProtocol.lean#L106-L120).

## 10. Constants and what is fixed versus abstract

| Object | Fixed value / generating rule | Lean source / status |
| --- | --- | --- |
| M31 modulus | `p=2147483647` | [V5ComponentCQM31TowerExact.lean:42–47](../../../AspisFormal/AspisFormal/V5ComponentCQM31TowerExact.lean#L42-L47) |
| Tower relations and cardinalities | `i²=−1`, `u²=2+i`, `v²=u`; `card(K)=p⁴`, `card(E)=p⁸` | [V5ComponentCQM31TowerExact.lean:12–22](../../../AspisFormal/AspisFormal/V5ComponentCQM31TowerExact.lean#L12-L22), [WideTower.lean:62–76](../v8-wide-reference-20261005/lean/WideTower.lean#L62-L76) |
| Transcript block | 32 bytes, little-endian rank; 256-bit range | [V19/SourceDuplexStep.lean:11–14](../v8-full-view-zk-20260912/lean/AspisV8R19/SourceDuplexStep.lean#L11-L14), [C/ModuloField.lean:18–23](../v8-r0-close-20261007/lean/R0C/ModuloField.lean#L18-L23) |
| Scalar moduli | `p⁴`, `p⁸`, `p⁸−1` with rank +1 for γ | [P/SemD2.lean:179–184](../v8-r0-sem-proof-20261008/lean/R0P/SemD2.lean#L179-L184), [C/ModuloField.lean:75–81](../v8-r0-close-20261007/lean/R0C/ModuloField.lean#L75-L81) |
| Circle fallbacks | QM31 limbs `[0,0,1,0]`, `[1,0,1,0]` | [P/CircleSampler.lean:129–145](../v8-r0-sem-proof-20261008/lean/R0P/CircleSampler.lean#L129-L145) |
| Circle generator | `(2,1268011823)`, order `2³¹` | [CircleGroupOrder.lean:170–176](../../../AspisFormal/AspisFormal/CircleGroupOrder.lean#L170-L176) |
| Initial shape | message 1024; word `2²⁰=1048576`; blowup `2¹⁰=1024` | [Wide/InitialEncoder.lean:32–39](../v8-wide-reference-20261005/lean/Wide/InitialEncoder.lean#L32-L39), [V6EncoderDistance.lean:29–35](../../../AspisFormal/AspisFormal/V6EncoderDistance.lean#L29-L35), [P/Core.lean:18–20](../v8-r0-sem-proof-20261008/lean/R0P/Core.lean#L18-L20) |
| Initial polynomial halves | 512 natural coefficients each; degree ≤511 | [V5FriInitialCircleEncoderIdentity.lean:124–139](../../../AspisFormal/AspisFormal/V5FriInitialCircleEncoderIdentity.lean#L124-L139) |
| Stored domain | 18-bit fibre reversal; exponent `1024*(2*n+1)`; four slot formulas in §3 | [V7ExactOneFoldDomains.lean:36–58](../../../AspisFormal/AspisFormal/V7ExactOneFoldDomains.lean#L36-L58), [V6EncoderDistance.lean:31–35](../../../AspisFormal/AspisFormal/V6EncoderDistance.lean#L31-L35) |
| Fold factor | 4; `child=4*parent+slot`; message/fold exponents 0,1,2,3 | [V5ComponentCConcreteFoldLinearity.lean:168–171](../../../AspisFormal/AspisFormal/V5ComponentCConcreteFoldLinearity.lean#L168-L171), [V5ComponentCConcreteFoldLinearity.lean:205–211](../../../AspisFormal/AspisFormal/V5ComponentCConcreteFoldLinearity.lean#L205-L211) |
| Final shape | 256 natural coefficients; word `2¹⁸=262144`; degree ≤255; blowup 1024 | [Wide/FinalEncoder.lean:22–29](../v8-wide-reference-20261005/lean/Wide/FinalEncoder.lean#L22-L29), [Wide/FinalEncoder.lean:89–98](../v8-wide-reference-20261005/lean/Wide/FinalEncoder.lean#L89-L98) |
| First line nodes | `X(g^(2048+8192*rev18(u)))` | [V7ExactOneFoldDomains.lean:330–349](../../../AspisFormal/AspisFormal/V7ExactOneFoldDomains.lean#L330-L349) |
| Quarter and dual powers | `4⁻¹`; `[0,3,2,1]` | [R0/RoundNormalization.lean:22–26](../v8-wide-reference-20261005/lean/R0/RoundNormalization.lean#L22-L26) |
| Lanes | 29; semantic 0–15; mask-only 16–25; H1=26,G=27,D=28 | [P/Core.lean:18–20](../v8-r0-sem-proof-20261008/lean/R0P/Core.lean#L18-L20) |
| C2 replacement | exactly lanes 26 and 27; D remains in initial W | [P/SemView.lean:59–78](../v8-r0-sem-proof-20261008/lean/R0P/SemView.lean#L59-L78) |
| Claim dimensions | three points ×29=87; two circle endpoints ×29=58 | [R0/OpeningDefinitions.lean:21–28](../v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean#L21-L28) |
| Semantic coordinates | ten; row bits MSB first, reversed for eqWeight | [P/Core.lean:22–28](../v8-r0-sem-proof-20261008/lean/R0P/Core.lean#L22-L28), [P/SemView.lean:36–56](../v8-r0-sem-proof-20261008/lean/R0P/SemView.lean#L36-L56) |
| Inactive set | complement of 64×16 active-row mask bits in §6 | [P/CopyConstants.lean:30–31](../v8-r0-sem-proof-20261008/lean/R0P/CopyConstants.lean#L30-L31), [P/Copy.lean:239–245](../v8-r0-sem-proof-20261008/lean/R0P/Copy.lean#L239-L245) |
| Semantic mask degree | mask factors up to 26; ten sumcheck polynomials degree ≤27 | [P/MaskValue.lean:15–47](../v8-r0-sem-proof-20261008/lean/R0P/MaskValue.lean#L15-L47), [P/MaskProtocol.lean:93–102](../v8-r0-sem-proof-20261008/lean/R0P/MaskProtocol.lean#L93-L102) |
| PCS polynomial | degree ≤6; seven coefficients; six transmitted indices `[0,1,2,3,5,6]` are P1 proposal | [R0/RoundNormalization.lean:31–43](../v8-wide-reference-20261005/lean/R0/RoundNormalization.lean#L31-L43), [R0/OpeningDefinitions.lean:109–113](../v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean#L109-L113) |
| Round schedule | 32 total; 25 semantic, 2 circle, 5 opening | [P/MaskProtocol.lean:30–36](../v8-r0-sem-proof-20261008/lean/R0P/MaskProtocol.lean#L30-L36), [P/MaskProtocol.lean:139–151](../v8-r0-sem-proof-20261008/lean/R0P/MaskProtocol.lean#L139-L151) |
| Q22 | 22 distinct fibres from `2¹⁸`; low 18 bits of eight u32 words/block; eight block pairs; 64 draws | [V19/Q22WordScan.lean:13–21](../v8-full-view-zk-20260912/lean/AspisV8R19/Q22WordScan.lean#L13-L21), [V19/SamplerWords.lean:9–31](../v8-full-view-zk-20260912/lean/AspisV8R19/SamplerWords.lean#L9-L31), [C/V3/DuplexQ.lean:43–58](../v8-r0-close-20261007/lean/R0C/V3/DuplexQ.lean#L43-L58) |
| Analysis agreement cutoffs | initial 38229, final 9557 | [R0/ListsResponses.lean:72–79](../v8-wide-reference-20261005/lean/R0/ListsResponses.lean#L72-L79); proof-analysis constants, not additional runtime rejection tests |
| Analysis candidate cap | ≤100 | [R0/ListsResponses.lean:41–59](../v8-wide-reference-20261005/lean/R0/ListsResponses.lean#L41-L59); no runtime candidate enumeration is specified |
| R16 transport | matrix T from §3; I,pivot,π are parameters in its Lean module | [V16/BalancedTransport.lean:15–17](../v8-full-view-zk-20260912/lean/AspisV8R16/BalancedTransport.lean#L15-L17); no concrete R0 instantiation |
| Byte tags/labels/IV | P1 proposal, labels `a0..bf`; E=32 wire bytes | §9; not constants supplied by Lean |
| Merkle/hash/PoW | SHA-256 and arity 8 are implementation choices from PLAN; tree serialization/authentication adapter unresolved; no grinding/PoW condition in Accept | [R0/OpeningDefinitions.lean:109–113](../v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean#L109-L113), [F/Protocol.lean:127–135](../v8-r0-fs-20261006/lean/R0FS/Protocol.lean#L127-L135); no PoW round added here |

The abstractions relevant to implementation are precisely:

| Interface | Generic source | What R0P fixes / what remains open |
| --- | --- | --- |
| `D.points`, `D.inactive` | [R0/OpeningDefinitions.lean:21–28](../v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean#L21-L28); [F/Protocol.lean:34–48](../v8-r0-fs-20261006/lean/R0FS/Protocol.lean#L34-L48) | `SemView.openingStmt` fixes `openingPoints A` and `copyInactiveRows`; §6 gives both completely. |
| `W`, lane subfields, public data | [P/SemView.lean:59–78](../v8-r0-sem-proof-20261008/lean/R0P/SemView.lean#L59-L78) | Words are input functions; C2 replaces two of them. Subfield F, higher-lane subfields, and `PackBasis` are parameters, not a byte/parser definition. |
| Semantic integration | [P/SemD3Glue.lean:88–113](../v8-r0-sem-proof-20261008/lean/R0P/SemD3Glue.lean#L88-L113); [P/MaskSource.lean:17–41](../v8-r0-sem-proof-20261008/lean/R0P/MaskSource.lean#L17-L41) | Old `SemD3Glue.sourceData` has 24 semantic rounds; masked `sourceDataZ` uses 25 and `decisionZ`. Use the 32-row masked instance, not the old offsets. |
| Point-claim timing and endpoint timing | [P/MaskView.lean:180–192](../v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean#L180-L192) | 87 claims before z0; the earlier Y0 is absorbed but not related by a parser equality to row-27 Y. |
| Encoding, labels, IV, proof accessor | [FS2/Duplex.lean:61–72](../v8-fs-generic-20261006/lean/FS2/Duplex.lean#L61-L72); [P/MaskProtocol.lean:139–151](../v8-r0-sem-proof-20261008/lean/R0P/MaskProtocol.lean#L139-L151) | Supplied as `p`, `msg`, `decode`; no concrete byte profile is selected. P1 and its limitations are in §9. |
| Authentication | [F/Protocol.lean:127–135](../v8-r0-fs-20261006/lean/R0FS/Protocol.lean#L127-L135) | Route A has complete words and authentic=True. The compact Merkle route requires its own binding. |
| Encoder implementation | [Wide/InitialEncoder.lean:29–39](../v8-wide-reference-20261005/lean/Wide/InitialEncoder.lean#L29-L39) | Exact mathematical evaluator is fixed; FFT implementation and R16 composition are not part of this definition. |
| Polynomial-pair lift / quotient decoder | [R0/PolynomialPair.lean:34–58](../v8-wide-reference-20261005/lean/R0/PolynomialPair.lean#L34-L58); [Z/HonestView.lean:148–160](../v8-r0-zk-20261009/lean/R0Z/HonestView.lean#L148-L160) | Lift is uniquely computed by M⁻¹ and monomial truncation. Honest quotient is unique on-image; the total off-image decoder is noncomputable/unspecified operationally. |
| Hash oracle / failure behavior | [V19/SourceDuplexStep.lean:4–14](../v8-full-view-zk-20260912/lean/AspisV8R19/SourceDuplexStep.lean#L4-L14); [Z/HonestView.lean:34–40](../v8-r0-zk-20261009/lean/R0Z/HonestView.lean#L34-L40) | H is an arbitrary oracle; SHA instantiation is external. H1 ActivePole abort is ZR1 and has no honest-model element; do not turn Lean's total inverse into a policy for proceeding through that source abort. |

The formulas, 32 row assignments, verbatim acceptance predicate, constants, and P1 encoding proposal are the S1 deliverable. The flagged interfaces remain decisions/refinement work; no proof or source implementation is started here.

Documentation validation: all 32 rows and unique labels checked; all 184 Lean citation ranges checked; V1/V2/Accept compared verbatim with source; all 64 inactive-mask words compared with `copyActiveRowMasks`; expanded φ, the seven coefficient formulas, and the quarter constant checked. Cited Lean sources are unchanged from the recorded snapshot. No Lean/Rust build or proof was run.
