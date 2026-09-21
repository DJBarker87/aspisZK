# A quadratic channel reduction before the existing PCS path

Status: paper algebra and executed independent finite-field models. Not an implemented Aspis profile, source refinement, privacy theorem, or measured SBF optimization. This is the larger experimental track. The same-profile track is independent.

## 1. What the old obstruction actually forbids

R17 correctly showed that two distinct functionals cannot be evaluated from a single sum of their inputs. Merely averaging the quotient messages and weights is wrong. This proposal adds a verifier challenge and a degree-two sumcheck before reducing to one quotient. It does not assert the impossible identity or discard the G functional.

Let the original relation, after BOTH interpolant subtractions, be

    C = <q_R,w_R> + <q_G,w_G>.

The weights include the complete original image-residual terms. The following deterministic identities hold for arbitrary coefficient vectors, including malicious high coefficients. No image-zero or honest-generation premise is used.

Define

    q(X) = q_R + X(q_G-q_R)
    w(X) = w_R + X(w_G-w_R)
    P(X) = <q(X),w(X)>.

This polynomial has degree at most two, and P(0)+P(1)=C. Its coefficients are

    p0 = <q_R,w_R>
    p1 = <q_R,w_G-w_R> + <q_G-q_R,w_R>
    p2 = <q_G-q_R,w_G-w_R>.

The prover sends p0,p2. The verifier reconstructs p1=C-2*p0-p2, absorbs the complete message, and then obtains beta. The reduced claim is P(beta), concerning q_beta and w_beta.

This is one binary-domain sumcheck round, not an arity-four relation round. Its boundary is evaluation at 0 plus evaluation at 1. Do not use the existing fourth-root boundary function for this new polynomial.

## 2. Exact compact R18 functional

Write A for the ordinary R18 functional before image terms, E for the transported first MLE, H for sparse code-coordinate G. Then

    w_R = A + image_R
    w_G = A + kappa*(H-E) + image_G.

Their affine interpolation has base functional

    A + beta*kappa*(H-E).

Therefore the ONE ordinary compact evaluator uses point scales

    [(1-beta)*kappa, kappa^2, kappa^3],

and ONE sparse G evaluator uses scale beta*kappa. The original XOR12 fused point block accepts these first/third scales; it need not materialize A and E separately. Preserve the successor point and inactive/pivot correction. The inactive coefficient remains one, since (1-beta)+beta=1.

The image coefficients must be

    i0 = (1-beta)*tau   + beta*tau^3
    i1 = (1-beta)*tau^2 + beta*tau^4.

The contribution on a quotient remains

    i0*q[1023] + i1*(b*q[1022]-c*q[1021]).

Both original channels' image terms participate in these formulas. Neither an honest-generator assertion nor a zero high tail replaces checking. beta=0, beta=1, or a zero image coefficient is not an implementation exception: do not divide by or silently resample these values. Their security significance belongs in the probability analysis.

## 3. Raw openings and interpolation

Let raw_all=raw_R+raw_G be the existing gamma-batched packed opening. The new numerator is

    raw_beta = (1-beta)*raw_all + (2*beta-1)*raw_G.

This can also be computed as lerp(raw_all-raw_G,raw_G,beta). The new interpolant is I_beta=lerp(I_R,I_G,beta); the original chord L is unchanged. Thus q_beta=(raw_beta-I_beta)/L, and only one four-slot quotient fold is required per queried fibre.

ALL original C1/C2 canonical limbs must still be validated; both roots and paired authentication remain. The component OOD rows and gamma powers still have their old meaning. Do not reinterpret G as an MLE or drop its packed data simply because only one combined quotient is opened.

IMPORTANT CLAIM ORDER: the pre-channel claim C must still be constructed using both original functionals and their two respective interpolant subtractions. After reducing to P(beta), do not subtract a new interpolant contribution again. Replacing the whole preparation routine with an old one-channel routine would generally be wrong; only the later functional/quotient path becomes one-channel.

## 4. Candidate transcript and wire

Use a new profile from transcript initialization, for example

    AV8/R19/sparseG-T163/quadratic-channel-fold/research-v1

and independently pinned domain labels for the channel message and beta. A concrete order is:

1. Existing statement, C1/C2 roots, semantic messages, component point/OOD claims, gamma, inactive claim, kappa, functional descriptor, incoming claim, and tau.
2. The two canonical channel coefficients p0,p2.
3. A new beta challenge, with its actual duplex/rejection/cache behavior specified.
4. Existing first degree-six relation polynomial, alpha0 and work-nonce framing, now for q_beta,w_beta.
5. ONE Final256, absorbed before the actual q22 query selection.
6. One query-weight injection and the remaining three degree-six relation rounds.
7. Complete authentication, image, and final acceptance.

The old fixed field allocation is 953. Replacing 512 final fields by 256 and adding two channel fields gives 699: a reduction of 254 QM31 values, or 4,064 bytes in this fixed region. This is not a measured total proof length; actual frontiers and other framing remain source-dependent.

Suggested indexing, subject to source reconciliation:

    existing prefix:       [0,417)
    channel p0,p2:          [417,419)
    four relation rounds:  [419,443)
    Final256:              [443,699)

Old profiles must reject under the new parser. Keep original fixtures and negative regressions. A q22 schedule from an old proof cannot be reused as though challenges were unchanged.

## 5. Conditional soundness statement—and its real limitation

For a FIXED pair of quotient vectors and weights determined before beta, a false incoming claim makes the difference between the sent polynomial and the genuine P a nonzero polynomial of degree at most two. For a uniformly sampled beta in a finite field, at most two beta values can hide that difference.

This is a local 2/|F| statement, NOT an end-to-end Aspis bound. It requires proving the quotients/weights are fixed in the relevant pre-answer experiment. If an extractor only identifies q_beta after beta, that does not supply the missing pair. Joint commitment extraction, possible list sizes, gamma batching, code proximity, image validity, and the actual adaptive shared oracle must be addressed. Any list multiplicity or adversarial query budget belongs in the loss ledger. Do not copy the old R18 soundness verdict or assume independent uniform FS challenges.

The independent check exhausts every F31 quadratic whose boundary discrepancy is nonzero. There are 28,830 such polynomials, each with at most two roots; the maximum is attained. This checks the elementary counting claim, not the source probabilistic premises.

## 6. Privacy gate: two new observations are not free

The channel coefficients can contain witness-dependent information. Removing a Final256 does not by itself prove that the new view is less informative. Changed challenge chronology also prevents treating it as a projection of the old transcript.

At a fixed permitted pre-channel history, let Q_R and Q_G be the source linear maps from legal mask coordinates to quotient differences, with their affine offsets retained. The new rows include

    p0: w_R^T Q_R
    p2: (w_G-w_R)^T (Q_G-Q_R)
    final: F_alpha0 * ((1-beta)Q_R + beta Q_G).

They must be included together with all earlier messages, raw C1/C2 observations, point/OOD observations, later relation polynomials and publication/stopping behavior. Obtain the source maps from actual compiler fixtures and the real q22 law, not from a convenient independent query set.

Check the two genuine same-public witnesses, construct and independently verify the affine target correction, and then prove a universal compatible-image statement with a justified exceptional-event bound. Track the same remaining coins throughout. Both original quotient components may be needed in the proof even though only their affine combination is serialized.

If either new channel row yields a source-valid separator, retain and quantify it. Do not add an opaque hiding/rank premise to force the experiment to succeed. R18 remains the fallback profile while this separate experiment is assessed.

## 7. Tests supplied and next exact source targets

The executable model uses the R18 T163 map, all three source-shaped statement points, the actual sparse slot formula, the natural-basis chord transpose including its 513-coordinate intermediate, and both image residuals. It checks arbitrary quotient coefficients in 48 full-QM31 cases, including beta=0,1,-1, and checks commutation with all four dual folds.

Next bind those equations to the actual staged source and add the new field framing/challenge. Generate real proofs and reject invalid proofs. Then measure the complete primary SBF path immediately. Do not spend a large formalization run on the new profile before learning whether its implemented cost meaningfully improves the best unchanged-profile candidate.

This packet supplies the algorithm and proof targets; it does NOT assert that the candidate fits 1.4M CU.
