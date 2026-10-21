# Prover commitment continuation 7 — 2026-10-21

Branch `codex/cx-prover-commit7-20261021`, base `072b24afc`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit7-20261021/`.

## Exact cursor classification

`ProverCommitCursor.decoder_exhausted` identifies failure of the finite,
consuming sequential array decoder with `CommitReadsR1.Exhausted` whenever
`16 * L ≤ N`. The proof handles arbitrary word streams and every starting
cursor/retry state. It does not pad accepted limbs to sixteen words. It
proves the forward/reverse Kleisli iterations equal and transports the
finite suffix recursion to the actual `tryLimb`/`limbPos` definitions.

Focused env J **8243**: exit **0**, wall **2.09 s**, peak RSS
**4,034,836 KiB**, **zero swaps**; five verbatim audits use only
`propext`, `Classical.choice`, `Quot.sound`. Attempts 8240–8242 were
elaboration drafts, excluded. An unchanged-input preflight for 8243 was
refused before compilation; the proof was then corrected and 8243 used
normally. The refusal is not accepted verification evidence.

Further stage results, exact checklist changes and final audit follow below.

`ProverCommitSourceExhaustion.quotient_exhausted` transports the result to
exactly the existing two `wordsE` block carriers. Failure of the quotient
is **equivalent** to either stream's exhaustion. `caller_exhausted` shows
that the same caller equation required by the fibre transfer also suffices
for source exhaustion; there is no independent cursor premise once that
equation is proved. This does not prove the caller equation.

Accepted J **8245**: exit **0**, wall **2.76 s**, peak RSS
**4,170,036 KiB**, **zero swaps**, two standard-axiom audits. J8244 is an
excluded syntax draft. This closes the exact finite-decoder/cursor
classification sub-obligation, conditional source transfer stated explicitly.

## Typed caller interface and privacy endpoint

`ProverCommitCallerInstance.CallerLaw` is one named Prop with the two
canonical block budgets and an existential output-coordinate equivalence.
It requires the projected caller to equal the sequential decoder followed
by that equivalence on **every** pair of block-answer vectors. This permits
the source's actual cell order rather than requiring `Fintype.equivFin` to
be its enumeration. `fibres`, `exhaustion`, and `budgets` derive all previous
fibre, RExh, stream, counter, cell-count and block inequalities from it.
The caller law itself is not proved or installed as an axiom.

`PrivacyR1FinalProtocolCaller.privacy_R1_protocol_caller` is built directly
on `PrivacyR1FinalProtocolQuotient`. At the M31 image subfield, it replaces
those separate premises and free cF/L₁/L₂ parameters with this law, the
proved `quotientFibreSize`, and the canonical `L₁/L₂`. Its conclusion is the
same experiment, simulator and error expression specialized to those two
counts, including the strict 2^-100 bound. Wire execution joins and builder
premises remain explicit. It does not assert universal source read coverage.

Accepted final J **8250/8253**: exit **0**, wall **2.55/3.25 s**, peak RSS
**4,045,904/4,074,780 KiB**, **zero swaps**; seven standard-axiom audits.
J8249 is the accepted, narrower exact-order prototype; the final law
explicitly supports the required coordinate bijection. Other drafts
8246–8248 and 8251–8252 are excluded. All literal attempted sources are
retained. Only this branch's new modules/objects are installed or replaced;
SourceIdentification, RustRuntimeJoin and PrivacyR1FinalRelease are untouched.
