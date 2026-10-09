# Three-helper cover to actual quotient claims

Continuation base: `e90e7338656f221c9a1bbde90d533ba94d002014`, branch
`research/v8-no-work-100-20260907`. This note concerns new deterministic
interfaces only. The new endpoint is kernel-checked; no production code or
previously checked leaf is changed.

## Statement and causal boundary

`ThreeHelperClaimCover.quotient_cover_dichotomy` consumes the unchanged
optional `earlyC1 received = some p26` and the selected three-helper theorem.
Write `S` for that object's actual complete-fibre own support. It returns:

- fewer than three good nonzero gammas in the supplied gamma set; or
- one full original-code coefficient tuple `P29`, with C1 projection exactly
  `p26`, which covers every image-valid quotient candidate at the stated
  distance, for every subsequently supplied checked OOD datum.

The dense tuple is chosen before OOD data, gamma, candidate, component claims
or relation strategy. The three helper words may depend on C2, which itself
may be chosen after the early semantic challenges; only the C1 projection is
identified with the pre-C2 object. The theorem does not move helper coefficients
back through those earlier challenges.

For the actual natural encoder and actual stored fibre map, the implication is

```
image(Q) = 0
and distance(encode(Q), virtual(data, rawBatch(gamma))) <= 4 * 15334
    => data.original(Q) = sum(lane=0..28, gamma^lane * P29[lane]).
```

No received polynomiality, candidate-family membership, successful provider,
or pre-existing quotient anchor is assumed. Anchor existence and the
acceptance-to-closeness implication are not supplied here.

## Exact support and algebra interfaces

`rawBad_card_le_full` restricts the actual original-word discrepancy to S,
using the already proved `fibreBad_raw_eq` orientation/index bridge.
`close_original_on_support` then uses the general
`SelectedQuotientOriginal.fibreBad_card`: reconstruction adds at most two
chord-pole fibres, including when the totalized virtual word divides by zero.
Thus `4*15334 + 2 = 61338`, exactly the existing helper-cover allowance.
There is no assumed globally nonzero chord denominator.

`good_of_close_image` additionally shows that every such quotient at any
gamma belongs to the same prefix-fixed helper-good set. This is relevant to
the sparse branch: it is not silently discarded or replaced by a dense tuple.
`good_subset` exposes that the set lies in the original challenge domain.

`join_projection` and `batch_join` are literal coefficient equalities. They
join 26 C1 messages and three helper messages without changing gamma powers:

```
batch(gamma, join(p26,h3)) = c1Batch(p26,gamma) + gamma^26 * helperBatch(h3,gamma).
```

The full component error polynomial still has degree at most 28, by the
existing `ClaimTransport.component_error_degree`; a wrong coefficient makes
it nonzero by `component_error_nonzero`. This helper-cover reduction does not
turn a false C1 point claim into a degree-two error. The existing degree-25
counterexample remains applicable.

## Scope and unchanged obligations

The optional early-C1 `none` branch is outside this conditional result. The
full joined tuple is not asserted to have the old width29 own-support bound
245609; that number is used for C1 alone. No full-view hiding, authenticated
root-to-word coupling, efficient tuple construction, Gao decoding, checked
payment witness, adaptive relation probability or Fiat–Shamir lift is proved
by this leaf. In particular, accepted far candidates are not discarded.

No transmitted values or verifier operations are added. The unchanged body
census remains `697*16 + 52 + 24 + 22*621 + 2*296*26 = 40282` bytes. This is
an analysis radius, not a field/domain/query/profile change, and gives no CU
or proving-time measurement. No work/grinding credit is used.

## Reproduction and evidence

New target: `experiments/ThreeHelperClaimCover.lean`.

```
bash docs/research/v8-no-work-100-20260907/experiments/run_three_helper_claim_cover.sh \
  docs/research/v8-no-work-100-20260907/experiments/three-helper-claim-cover-v5.log
```

This is the recorded successful command. A justified new replay must supply
a fresh log filename; the runner refuses to overwrite existing evidence.

The runner checks the whole imported research source closure against the base
commit above, and the borrowed V7 source closure against immutable
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. It records every imported source
and olean SHA-256 before and after the focused run. The pinned cached Mathlib
commit is `81a5d257c8e410db227a6665ed08f64fea08e997`; no concurrent uncommitted
main theorem is imported. The ordinary local run uses Lean `-M7000` plus a
7-GiB aggregate-child RSS stop; no cold dependency rebuild is launched.

Status: **formal proof complete for this deterministic endpoint**. The v5
leaf and its provenance postflight both exited zero. Its ten audited public
declarations, including `batch_join`, `good_of_close_image` and
`quotient_cover_dichotomy`, depend only on `propext`, `Classical.choice` and
`Quot.sound`. There are no new axioms, retained `sorry` or correspondence
premises standing in for the support/image/coefficient identities above.

| Focused attempt | Exit | Wall seconds | Peak RSS bytes | Swap | Result |
|---|---:|---:|---:|---:|---|
| v1 | 1 | 27.55 | 5,561,630,720 | 0 | Missing explicit known `NeZero 2`; final batch type mismatch |
| v2 | 1 | 22.20 | 5,580,308,480 | 0 | Full-type diagnostic isolated two Fin29 enumeration instances |
| v3 | 1 | 31.89 | 5,476,401,152 | 0 | Symbolic finite-set transport added; terminal type traversal remained |
| v4 | 1 | 24.60 | 5,556,387,840 | 0 | Only the field alias unfolded; terminal traversal remained |
| v5 | 0 | 25.90 | 5,684,838,400 | 0 | All interfaces checked; standard-only axiom audits |

The successful source SHA-256 is
`0449aedbb283b715340d8d99d5d5d0669cdc08b4f8c7789fe1a9943eb3a9c3c2`;
olean SHA-256 is
`c1b584180a344a94695e04e00b5c38fa4b63602c146bcae4effeffddd2ec00c5`;
runner SHA-256 is
`ceb2372489fe01ffa0e1a4eba4648144257a02ca25a337a752780648bd077d24`.
Lean is 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
The observed concurrent main revision was
`c7347eefcf767c375040f8f73160995a7886e3ae`; it was not substituted for the
immutable borrowed-source pin.

The elaboration fix is not a field or security change. `ClaimTransport.batch`
uses `Fin.fintype 29`, whereas the selected scalar helper inherited a
Simplex-category `Fintype` on the identical carrier. The new proof transports
their finite sets via subsingleton equality, without reducing an enumeration.
After that transport and the explicit K alias, the full printed expression
shapes match. Only the last `exact split` uses a scoped recursion depth 400
to traverse the expanded field-parameter type; global depth stays 200,
heartbeats stay 50000, and the memory limit is unchanged. The four failed
attempts are retained as logs, not claimed results.

The next consuming endpoint is the parent's causal image/ordinary/OOD game
composition, with this prefix-fixed P29 and the sparse gamma membership
implication. That composition must separately charge the sparse branch,
retain the full degree-28 claim error and keep far accepted recovery failures
visible.
