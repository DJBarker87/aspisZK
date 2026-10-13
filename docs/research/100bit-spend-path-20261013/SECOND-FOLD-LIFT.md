# Reusing the existing decoder for the second fold

Root design, 2026-10-13. This replaces the proposed new interpolation instance
in `SecondFoldBudget.lean` on the preferred proof path. It does not yet claim a
compiled R1 binding theorem.

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

Source/formal work still required:

1. Prove the final-domain quartet identities for `storedFirstLineX18` and
   identify the runtime's depth-two node with `T4(x)`.
2. Instantiate the existing `naturalCoefficientPolynomial_eval_radix4`
   identity, coefficient injection L, and averaging projection P.
3. Prove the complete-quartet cardinality and descent lemmas, then wrap the
   existing matched-response theorem. No new large certificate is needed.
4. Connect the runtime channel recovery and fold to those encoders;
   `lean/LineFold.lean` already proves the field recovery identities.
5. Complete the two round-polynomial comparisons, direct joint-list binding,
   and the new Fiat--Shamir schedule/source correspondence.

Relevant existing sources are `Wide/FinalEncoder.lean`,
`Wide/MatchedInstances.lean`, `R0/ListsResponses.lean`, and
`AspisFormal/V5FriConcreteEncoderApplicability.lean` (natural coefficient
radix-four expansion). These are mathematical dependencies, not evidence that
the final R1 theorem has already been compiled.

The abstract repeated-support cardinality and projection-descent steps now
compile in `lean/RepeatedLift.lean` (five standard-axiom audits). Its mean
identity and encoder overlap remain explicit hypotheses; the concrete E256
instantiation listed above is still pending. The exhaustive source lift gate
is recorded in `evidence/second-fold-lift-v2/`.
