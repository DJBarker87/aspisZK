# Strong early C1 enters the fixed family

Status: kernel-checked as one focused leaf on the capped Tailscale NUC.
Source: [EarlyC1StrongFamilyBridge.lean](experiments/EarlyC1StrongFamilyBridge.lean).

## Exact deterministic bridge

`complete_fibre_support_supplies_symbols` proves that every complete fibre
in the own support of a C1 tuple supplies four distinct stored symbols in
`V7FixedWidth29TupleList.c1JointAgreementSet`.  It uses the literal
`fibreEmbed (f,s) = 4*f+s` injection and all 26 C1 lanes.  Consequently,

    4 * complete_fibre_support <= joint_original_symbol_support.

`some_early_member` then consumes the definitional support theorem for the
fixed early object:

    earlyC1 received = some p
      -> 245609 <= complete_fibre_support(received,p)
      -> 982436 <= c1JointAgreementSet(received,p).card
      -> p in EarlyC1Family.family received.

The family threshold is 38,228 symbols, so this implication has a large
deterministic margin.  It introduces no late C2 word, lambda, chi, gamma,
provider result, final polynomial, acceptance event, or decoder-success
premise.  The object remains fixed solely by the early committed C1 word.

`some_early_is_base` composes the new membership theorem with the existing
`EarlyC1Family.member_is_base`.  When every received C1 symbol is fixed by
the M31 projection, all recovered message coefficients are fixed by that
projection as well.  This reuses the selected V7 encoder overlap theorem on
the candidate's own support; it does not assume same-support recovery or a
per-lane decoder filter.

## Consequence and limits

This removes a duplicate interface between the fixed-early higher-Y theory
and the selected payment/family endpoints.  Whenever `earlyC1` returns a
tuple, the existing at-most-100 family, collision alternatives, and
base-field descent machinery can consume that exact tuple.

It does **not** prove that `earlyC1` returns `some` on every accepting proof,
that a family member is selected by a resource-bounded extractor, or that
the selected semantic/copy/payment residuals hold.  The no-early and
postselected/incoherent branches remain part of the global soundness gap.
The theorem adds no probability term and gives no Fiat--Shamir or privacy
claim.

No verifier message, proof value, challenge, query, or commitment changes.
The proof-body census remains 40,282 bytes.  This is extractor mathematics,
not a CU or prover-time optimisation.

## Focused verification

Only `EarlyC1StrongFamilyBridge.lean` was compiled.  V1 exposed excessive
elaboration of a mapped product support.  V2 replaced that construction by
the already checked generic fibre-cardinality theorem, then exposed two
classical `Finset.filter` decision-instance mismatches.  V3 transports the
two propositions explicitly and passed without changing a theorem
statement, numerical threshold, import, or resource limit.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 3.11 | 6,659,732 | 0 | mapped-support elaboration reached depth 200 |
| v2 | 1 | 2.66 | 6,666,772 | 0 | only classical filter-instance transport remained |
| v3 | 0 | 2.77 | 6,704,536 | 0 | all three declarations standard-only |

Lean 4.32.0 ran with `-j1 -M9500` under MemoryHigh 8 GiB, MemoryMax
10 GiB, MemorySwapMax 0 and CPUQuota 200%.  The v3 preflight and postflight
both passed 995 pinned entries and recorded `PROVENANCE_UNCHANGED=true`.
No dependency or package replay ran.  Transport used Tailscale numeric IP
`100.108.41.90`; `nuc.local` was only the pinned SSH host-key alias.

The three v3 declarations audit only to `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx` or new axiom.  Failed-attempt `sorryAx`
lines are diagnostic and are not retained as successful evidence.

Inherited research cache pin:
`289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Borrowed V7 source pin:
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

| Artifact | SHA-256 |
| --- | --- |
| Green source / v3 snapshot | `65ec73b0bbb5a175503ee8454369c1c818310f2a4abd46e6fdc85f7a04f983a1` |
| Green olean | `88d6b186887142d8b92219e599b9a85f564b726cadb4aad587b1c447467bdd81` |
| V3 manifest | `9450afcac2bd2ba7f60849e456c6358953b58251e49e75da744c5055021a09b5` |
| V3 log | `1a0441320ae9a50b8f385a480865f430d5954bac05b6f48f0613eb570ab439e3` |
| Frozen runner | `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52` |

All three attempt source snapshots, manifests, and logs are retained under
`experiments/early-c1-strong-family-nuc-vN`.
