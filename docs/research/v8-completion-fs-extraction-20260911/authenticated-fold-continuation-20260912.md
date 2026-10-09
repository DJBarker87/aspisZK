# Authenticated record folds and continued oracle histories

Base: `8c606d9b0641892f38ad824caad0cdba8b7366ac`.
Branch: `research/v8-completion-fs-extraction-20260911`.
Research only; no protocol, accepted-body, production or CU change.

## New constructed connection

`SameBodyAuthenticatedFold.same_body_authenticated_fold_or_failure`
constructs decoded records from the functional Merkle run's own body. For
each of its 22 query ordinals, it proves that the record's actual quotient/fold
calculation equals evaluation of the folded virtual quotient of the two
commitment-prefix words. Alternatively, it retains exactly the previous
shared truncated-digest collision, C1 late-target hit or C2 late-target hit.

The proof composes the checked same-body slot producer with
`SelectedPackedQueryBridgeV3.matching_fold` and
`QueriedResidual.success_fold`. The latter consumes the checked ordered
inverse constructor. There is no `observedWord`, supplied total-word equality,
polynomiality, image-validity, successful decoder or witness premise.
The zero polynomial parameter of `SelectedReceivedOracle.oracle` does not
claim the received word is zero: its folded received-word component is the
one used here.

### Premise / producer boundary

| Input | What is constructed or still required |
|---|---|
| Submitted body, roots and record ordinals | Same functional `SuccessfulMerkleRun`; literal body record projection derived |
| Decoded 621-byte records | Constructed by `parseRecords`; canonical success remains a check premise |
| Total component batch | Constructed by `prefixBatch` from two prefixes and these body roots |
| OOD/chord data, including gamma | Same `Data` used throughout; source construction from fixed fields/transcript remains open |
| Query positions | Same vector for Merkle and fold; actual transcript sampler producer remains open |
| Inverse arrays | Successful `LineNormBuffer.inverseLines` required; no totalised-zero substitute |
| Alpha | Arbitrary field value, including zero; no false early-fixing assertion |
| Prefix chronology, shared hash answers and leaf/node log inclusion | Still explicit historical authentication premises; probabilities uncharged |
| Functional Merkle success | Not yet derived from literal Rust success |

This is a deterministic functional bridge, not full same-body verifier closure,
an efficient extractor, a new soundness bound or a payment-acceptance theorem.

The dependent `SameBodyAuthenticatedResidual` endpoint additionally constructs
all same-ordinal residual equalities and transports the entire expression
`prior - rho * sum (residual[i] * rho^i)` to that same prefix quotient. The
final polynomial, prior discrepancy and rho are arbitrary pointwise arguments;
the theorem does not pretend they were fixed earlier than their real selection.
This preserves the degree-q-shaped batch and the authentication alternative.
It still does not equate the actual source's positive `foldl` increment and
updated functional to this finite sum; that executable-algebra link remains.

## Oracle histories now extend past C2

`FSAuthenticationSuffix.continueRun` executes a bounded, adaptive later script
from the actual oracle state returned by `constructBoth`. Its selector receives
the completed early prefix, not future tape answers. The resulting theorem
`continued_prefix_answers` constructs both chronological cut prefixes as exact
takes of the **later** log, and proves their answers consistent with its cache.
It does not take inclusion, cache consistency or independence as premises.

Early and later aborts remain distinct; a later abort retains its full log and
is not verifier acceptance. A control repeats an earlier query, makes a new
query and aborts: all 10 calls are logged, only 7 are fresh, and the original
prefix lengths 1 and 7 remain unchanged. This is a model control, not a payment
fixture or randomness-law test.

The old `RawHashInput`/`Digest208` encoding conversion and concrete opening
script are still missing. Consequently the historical authentication premises
are not yet discharged merely by placing these two files next to each other.
Actual source/adversary coupling and a resource-bounded probability lift remain
separate obligations.

## Checks and exact scope

* Fold leaf: Lean 4.32.0, commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`; exit 0; runner wall 2.918s;
  time-v peak RSS 6,671,652 KiB; swaps 0. Printed axioms are only `propext`,
  `Classical.choice`, `Quot.sound`.
* Fold source SHA256:
  `953550659917c130eb7b21317f25d370f9085c1536cafa1d86fa745360dc65d3`.
  Evidence: `results/v8-completion-fs-extraction-20260911/auth-fold-historical-v1/`.
* Residual consumer: same historical toolchain; exit 0; runner wall 3.069s;
  peak RSS 6,675,840 KiB; swaps 0; standard axioms only. Source SHA256:
  `e8d721782b5fc2ff411bf792d01b84de6e21042ab3e9d22fc4994817c4fdc0a9`.
  Evidence: `results/v8-completion-fs-extraction-20260911/auth-residual-historical-v1/`.
  Both earlier leaf receipts/artifacts were validated, with all import hashes
  checked before and after compilation by the strengthened runner.
* NUC via Tailscale; separate output; MemoryHigh=8G, MemoryMax=10G,
  MemorySwapMax=0, RuntimeMaxSec=600. No old-cache edits. Prior slot source,
  artifact and compile receipt are hash-validated before import. The original
  1,115-file inventory and 28-file supplement were validated before the run
  and independently again afterwards.
* This is a **historical cached-import leaf check**, NOT a patched historical
  dependency rebuild or fresh kernel replay. The restored supplement retains
  its historical post-run-observation status.
* FS suffix: independent seven-module first-party source closure compiled
  with Lean 4.33.1, reusing pinned Std/toolchain only. All exits 0; endpoint
  standard axioms only. Evidence:
  `results/v8-completion-fs-extraction-20260911/FSAuthenticationSuffix-t7drzozt/`.
  Fresh kernel replay of this new root is NOT RUN. Agent leaf evidence is
  separately retained, not described as another independent kernel.

Reproduce the small source closure from this directory:

```sh
python3 FocusedLeaves.py --root FSAuthenticationSuffix
```

For the historical target, use `HistoricalLeaf.py` with the pinned overlay,
package, manifest and supplement described in `authentication-connection-20260912.md`,
the new fold source, a fresh output, and `--prior-leaf` pointing at the validated
slot-leaf output. Run inside the documented capped Linux scope. Actual commands,
search path, compiler and input/output hashes are in the retained receipt.
These imports are not portable by copying only their `.olean` files: the
source/dependency provenance checks are required.

The runner now rejects nested shadow `.olean` artifacts in prior output
directories and rechecks import hashes after compiling. A read-only check of
the already finished v1 directories found only the expected single module,
receipt and log; the unchanged proof was not replayed just to test the runner.

## Remaining target

The next consumer is the actual positive scalar/query-functional update and
its carried terminal. This must use these constructed folds and the same final
fields, not an independently supplied opened-value array. The full objective
remains `Pr[actual acceptance AND checked permitted-access extraction fails]`.
No global numerical bound is supplied here. Body maximum stays 40,282 bytes;
grinding credit stays zero. Full-view ZK and complete-transaction CU remain open.
