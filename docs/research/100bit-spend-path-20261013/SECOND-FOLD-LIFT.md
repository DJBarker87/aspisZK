# Reusing the existing decoder for the second fold

Root design, 2026-10-13. This replaces the proposed new interpolation instance
in `SecondFoldBudget.lean` on the preferred proof path. The concrete algebraic
chain now compiles through `ConcreteBinding.binding`; this is not a
probabilistic, source-correspondence, or Fiat--Shamir theorem.

Let `E256` be the repository's exact final encoder: 256 natural coefficients,
262144 distinct line nodes, and overlap at most 255 for unequal messages.
Group its stored coordinates into consecutive quartets. For parent `v`, write
the nodes as `[x,-x,-y,y]`, with `z = T2(x)`, `T2(y) = -z`, and common
parent node `t = T4(x) = T4(y)`. Here `T2(X)=2X^2-1` and `T4=T2∘T2`;
the common quantity is not the ordinary fourth power of the nodes.

For a 64-coefficient message `m`, define `L(m)[4d]=m[d]` and set the other
three coefficient slots to zero. Define `E64(m)(v)` by evaluating its natural
polynomial at `t`. The existing natural-basis radix-four identity gives

    E256(L(m))(4v+s) = E64(m)(v),  for all four slots s.

For a 256-coefficient message `a`, let `P(a)` keep only slots divisible by
four. If `h0..h3` are its four coefficient lanes evaluated at `t`, its quartet
is

    h0 + x*h1 + z*h2 + x*z*h3
    h0 - x*h1 + z*h2 - x*z*h3
    h0 - y*h1 - z*h2 + y*z*h3
    h0 + y*h1 - z*h2 - y*z*h3.

The average is `h0`. Therefore `E256(P(a))` equals the average at every
coordinate of that quartet. If `E256(a)` is constant on a union `4S` of
complete quartets, then `E256(a)` and `E256(P(a))` agree on `4S`. When
`4*|S| > 255`, the existing overlap theorem forces `a=P(a)`. Thus every
message matching a repeated word on enough full quartets descends through L.

Now fix four arbitrary words `g_s` of length 65536. Lift each by repetition:
`g_s↑(4v+j)=g_s(v)`. A second-fold response `(f,S)` with `|S|≥2390` becomes
the first-fold response `(L(f),4S)` to the lifted four words. It has agreement
at least 9560, exceeding the existing strict threshold 9557.

Apply `Wide.MatchedInstances.exactFinal_bad_response_challenges_card_le`
to these fixed lifted words. Its bad set has at most 9396508281246 elements.
Outside that set the response has four matching component messages `a_s`,
each agreeing with `g_s↑` on every point of `4S`, and

    L(f) = a_0 + alpha*a_1 + alpha^2*a_2 + alpha^3*a_3.

Each component descends by the average/overlap argument above: `a_s=L(b_s)`.
Injectivity and linearity of L then give

    f = b_0 + alpha*b_1 + alpha^2*b_2 + alpha^3*b_3,
    E64(b_s)|S = g_s|S.

This supplies precisely the matched-response property for the second fold.
It reuses the existing challenge cap (about 2^43.1), rather than the smaller
uninstantiated numerical cap (about 2^36.8). In WideExact both are far below
the q22 error; the larger existing cap is sufficient. No additional Johnson,
list-size, or interpolation-density premise is introduced.

For R1, let M be the original matching queried fibres. If `|M|≥9558`, its
set of second-fold parents S has at least 2390 elements. The second matching
decomposition reconstructs a 256-coefficient message matching the committed
intermediate word on all four children of S, hence on M itself. The first
fold's existing response extraction then applies on M, restoring the original
word on at least `4*9558=38232` coordinates (the initial cutoff is 38230).

The concrete chain now compiles on the NUC:

1. `Line18Geometry.lean` proves the actual `storedFirstLineX18` quartet
   geometry and its embedding in the challenge field.
2. `ConcreteProjection.lean` connects natural evaluation to the existing
   polynomial encoder, proves sparse-lift and mean identities, and uses the
   existing overlap cap to prove descent.
3. `SecondFoldMatched.lean` transfers the existing exact-final matched-response
   theorem with its unchanged 9,396,508,281,246 cap.
4. `SecondFoldRestoration.lean` derives all inverse-coordinate nonzero facts
   from stored-domain injectivity and restores complete quartets.
5. `TwoFoldExtraction.lean` combines both folds and the existing width-29
   theorem to obtain a member of the literal list `Lambda W`.
6. `ConcreteBinding.lean` uses that same candidate through both round
   comparisons and the direct functional comparison.

The final extraction theorem assumes the two matching field equations on a
support of size at least 9558 and exclusions from the three decoder bad sets.
The binding theorem additionally assumes the accepted round-boundary and
final-pairing field equations and the comparison bad-set exclusions. It does
not assume encoder overlap, inverse correctness, a new decoder, candidate
uniqueness, or that the extracted candidate belongs to an abstract supplied
list: those algebraic facts are now derived from the existing concrete code.

The remaining connections are the Rust-to-field formulas (including the
runtime depth-two node), authenticated commitment binding, the query and rho
sampling rows, the actual functional constructors, semantic extraction, and
the new Fiat--Shamir instantiation. See `CONCRETE-BINDING.md` for exact theorem
scope, counts and receipts. No new large generated certificate was needed.
