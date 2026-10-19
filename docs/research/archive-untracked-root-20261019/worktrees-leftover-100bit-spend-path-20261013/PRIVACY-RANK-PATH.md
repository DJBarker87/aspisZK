# A concrete route through the privacy rank obligation

This is a root proof design and an executable prerequisite check, not a
zero-knowledge theorem or a production prover. The current fixtures use
deliberately reproducible, insecure entropy.

## Fixed-challenge algebra

Use F=M31, K=QM31, E=WideExact. All semantic challenges are in K; the opening
batching challenge gamma is in E. The source C1 columns are F-valued; H1, G
and D are K-valued. The row-to-coefficient map is D18.

The own-column observation map contains the inactive sum, three MLE claims,
the Libra functional, two circle evaluations, and 88 opened symbols. It is
K-linear on K words. Restricted to F words and expanded into F coordinates,
it has 113 rows; the inactive sum is the first. On balanced C1 masks the
remaining observation space has dimension 112 over F. On balanced H1 padding
it has dimension 94 over K (95 rows with the inactive-sum coordinate zero).

For gamma outside K, multiplication by gamma maps gamma^27 to gamma^28, so
these two elements form a K-basis of E. For every physical lane c, there are
unique u_c,v_c in K with

    gamma^c + gamma^27*u_c + gamma^28*v_c = 0.

`lean/DualPad.lean` checks the two coordinate equations and determinant
expansion. The determinant is gamma.c1 times the nonzero norm of gamma^27.
Consequently a source word r on lane c can be accompanied by u_c*r on G and
v_c*r on D to make the entire gamma-batched word zero. If r is in the kernel
of its own observations, both companion words are too. This kills all linear
opening-layer observations, including either number of folds, without an
assumption that gamma belongs to K.

The actual-proof gate checks three finite linear-algebra conditions:

1. Every one of the 16 eligible balanced C1 mask maps has F-rank 112.
2. The balanced inactive-row H1 padding map has K-rank 94.
3. Own-observation-kernel directions on the ten mask-only columns, with the
   two companion pads above, span all 1076 F-dimensions of the normalized
   round-chain space with initial sum and terminal value zero. The same
   image before fixing the initial sum has dimension 1080.

These are checks on public transcript challenges and query positions, not
tests of a particular witness difference. `--proof-rank-gate` derives its
inputs through the actual R1 semantic verifier and transcript. It also rejects
gamma in K, any semantic alpha equal to 0 or 1, and alpha_9=1/2.

## Why these are useful sufficient conditions

Here is the intended universal construction, which remains to be transcribed
and connected to the exact R1 payload.

Take two balanced semantic/helper word sets, and let Delta_c be their
difference on each semantic C1 or H1 lane. By conditions 1 and 2, choose an
allowed mask n_c with the same own-column observations as Delta_c. Then
r_c=Delta_c-n_c is in the full own-observation kernel, including the inactive
sum. Set

    n_G = -sum_c u_c*r_c,   n_D = -sum_c v_c*r_c.

These are legal balanced K-valued pad shifts. They have zero own-column
observations and make the shifted masks reproduce the complete batched-word
difference. Thus all non-round observations match, including both R1 round
polynomials and the 64-value final message. After the existing terminal
normalization, the remaining semantic-round difference has zero initial sum,
satisfies the chain identities, and has zero terminal value. Condition 3
supplies a silent mask correction for it.

The same condition 3 absorbs the nonlinear eligible-noise remainder: the
existing `R0Z.Chain.sRem_mem_chain0` proves the corresponding reference
remainder lies in the chain space. Its source/payload transport to R1 is an
explicit task, not implied merely by sharing field types.

A stronger simulator route uses zero non-round offset as a public canonical
representative, matches an honest balanced offset by the same construction,
and repairs its normalized round residual. If this establishes that the
normalized honest offset itself belongs to the mask image, an efficient
simulator can sample the public linear map's image and undo the public
terminal normalization. It need not choose an unknown valid witness. This
stronger offset statement and the exact output distribution must be proved;
the existing witness-independence theorem with `Classical.choose` alone does
not establish an efficient zero-knowledge simulator.

## Optional fail-closed prover route

An honest prover could generate an attempt entirely locally, check these
public matrix conditions exactly, and publish/upload only passing attempts.
This would change the honest prover, not the verifier or soundness budget.
It would avoid publishing a proof on a known rank-deficient transcript.
The measured proof-driven gate takes about 16.5 seconds on the NUC.

This is not a completed shortcut around the privacy proof. It still requires:

- a theorem that the checked conditions imply the exact payload image and
  an efficient simulator, including semantic normalization;
- a rejection/abort-aware ROM reduction, with fresh private attempt entropy,
  fresh commitments, and no publication of rejected attempts;
- an acceptance-density/termination argument, or an explicitly modeled
  bounded abort outcome, with all visible retry information accounted for;
- commitment hiding and oracle-programming/freshness bounds, and the
  source connection for the mask generator and observation matrices.

The general need to analyze accepted and aborted transcripts separately is
also discussed in [A Detailed Analysis of Fiat-Shamir with Aborts](https://eprint.iacr.org/2023/245.pdf).
That paper is a methodological reference; its theorem is not an instance for
Aspis.

## Evidence

The actual transfer proof with SHA256
`c1a233f9e91c7d0341c68738c1cbf8d659beb05b9b14f89c7d26134b65da064b`
passes all three checks. See `evidence/privacy-wide/proof-rank-gate-v3/` for
the exact source manifest, input hashes, challenge values, and capped NUC
receipt. Earlier tests on two fixed E-valued gamma choices also passed five
concrete witness pairs each. Those samples are supporting evidence; they
are not substituted for the universal construction or its ROM reduction.
