# V7 K1.3 direct-ROM route status

## Decision

The candidate-directed K1.3 direct-ROM route is **not** the release route for
malicious-prover knowledge soundness.  It remains useful as algebraic and
scheduler research, but it must not be used to discharge the final V7
classical-random-oracle theorem.

The release route is:

```text
Tag-73 Fiat--Shamir acceptance
  -> K1.6 exact same-tape state-restoration compiler
  -> legal interactive Tag-73 execution
  -> K1.2 / K1.3 / K1.4 / K1.5 interactive extraction stages
  -> valid spend witness
```

This is the route implemented by the exact fixed-instance K1.6 closure in
`AspisFormal/K1/V7Tag73ExactFixedK16Closure.lean`.  Its compiler loss is the
explicit scheduler expression `(F + choose(F, 2) + F * G) / 2^256`; it is not
an imported BCS coefficient.

## Why the direct route cannot be the final proof

`V7Tag73K13ViewPrefixFactorization.lean` asks for a pre-query view determined
by a prefix which excludes the query-batch random-oracle answer.  That is not
true for an arbitrary Fiat--Shamir prover merely because the verifier assigns
the coordinate a later logical role.  A prover can query the public SHA input
itself before emitting the proof, learn the answer, and choose its later proof
material accordingly.  A verifier cache hit then consumes no new answer.

The scheduler results correctly model that case; see the existing
first-exposure analysis in
`docs/research/v7-first-exposure-role-classification-20260828.md` and the
actual-law source model.  Classifying adversary-first exposure as a negligible
event would be unsound: it can be deliberate.

This is not a flaw in the Tag-73 transcript.  It is the ordinary reason a
Fiat--Shamir proof needs a forking/state-restoration compiler argument rather
than a claim that an adversary did not query a public oracle input.

## What is retained

The following work remains valid and feeds the interactive stages:

- K1.3 algebra, circle/list-decoding and finite-field accounting;
- literal parser, transcript schedule and pre-query snapshot facts;
- the small source projection
  `snapshot_query_batch_prechallenge` and its Aeneas extraction at
  `aeneas-verif/v7-k13-prechallenge-snapshot-source-20260913`;
- the K1.2 typed two-tree/208-bit certificate work;
- K1.6's exact same-tape compiler and its fixed-instance operational input.

In particular, the source snapshot establishes what the deployed verifier
computes at the query boundary.  It does not, and cannot by itself, establish
that an arbitrary prover chose that state before learning a public
Fiat--Shamir answer.

## Remaining formal work on the release route

1. Instantiate `ProofRelevantK12ToK15Stages` for
   `ExactFixedSchedulerK12ToK15Input`, beginning with the exact two-tree,
   shared-topology 208-bit K1.2 certificate.
2. Connect the K1.2 output to the existing interactive K1.3 circle/list
   decoder, then the K1.4 coherent-chain selection and K1.5 spend-witness
   recovery.
3. Prove the four resulting interactive-stage error bounds and install them
   in `exact_fixed_tag73_k16_classical_rom_aok_raw`.
4. Compose the accepted-source/Aeneas bridge with the production Pool caller.

No direct-ROM fibre-invariance premise is permitted in the release capstone.
