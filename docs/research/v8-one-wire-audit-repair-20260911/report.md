# V8 one-wire audit-repair report

Audited commit and repair base: `30a303a344dbb42e24ad8f42a8804819747942bc`.
The supplied audit zip SHA-256 is
`fb7687e514a677b0061ec114a86e832d65afcf8b3fe12e935494ae8dfd6cf62f`.

## Reproduced finding

**PASS: the original same-body finding is reproduced.** The supplied Python
diagnostic was rerun and its generated JSON matches the supplied result byte
for byte: 17,845 Merkle-loop comparisons, 2,275 valid fixtures, 15,570
negative mutations, q22/depth18 frontier 296, 40,282 maximum body bytes, and
a canonical fixed-field mutation that changes parsed `Wire.values` while
preserving roots, nonces, records and frontiers. This is a representation
diagnostic, not an accepted proof or payment forgery.

A pinned Lean signature audit confirms that
`successful_complete_selected_wire_constructs_ideal_execution_or_auth_failure`
takes an independent `p : Program 22` and `body`. Only its roots are linked by
`rootBound`. Thus it is retained as a conditional composition, but its
docstring is corrected: it is not a one-body source-refinement theorem.

## Repair

`OneWireConsumedFields.lean` constructs all fixed relation fields from one
successful `SelectedWireBytes.parse body`:

| Fields | Same-body projection |
|---|---|
| 0..270 | opaque outer-semantic values |
| 271..357 | three 29-lane claims |
| 358 | inactive claim |
| 359..416 | two OOD answer vectors |
| 417..440 | four compact six-value responses |
| 441..696 | final256 |

`fixedAt_decoded` and its specialised theorems prove exact canonical decoding
at literal body offsets. `relationFields` is transparent and contains no
Program, acceptance, ideal execution, witness or coherence certificate.

Focused Lean 4.32 v3 passed on the pinned NUC overlay: exit 0, 2.86 s,
6,702,864 KiB peak RSS, zero swaps. The five audited declarations use only
`propext`, `Classical.choice`, `Quot.sound`. Two rejected source attempts are
retained: wrong module prefix (v1) and wrong codec namespace (v2). The
signature/axiom audit passed: exit 0, 12.99 s, 6,564,532 KiB, zero swaps.

## Verdict table

| Gate | Verdict |
|---|---|
| Same-body fixed-field construction | PASS, narrow leaf |
| Functional same-body endpoint | FAIL / unconstructed |
| Causal consistency across histories | NOT RUN |
| Functional Merkle/opening result | PASS, retained conditional result |
| Actual Rust-to-functional refinement | BLOCKED |
| Authenticated C1/C2 prefix timing | NOT RUN |
| First-party source rebuild | BLOCKED |
| Fresh kernel replay | BLOCKED |
| Focused axiom hygiene | PASS |
| Frozen-statement adequacy | PASS for specification; endpoint unproved |
| External checker validation | BLOCKED |
| Mutation/nonvacuity test | PASS, representation scope only |
| Allowed-access checked payment extraction | NOT RUN |
| Global probability composition, adaptive ZK, all-reachable CU | OUT OF SCOPE / open |

The `leanchecker` binary exists in the pinned environment, but the attempted
`leanchecker --help` exited 137 after 26.8 seconds. It was not retried
unchanged. The source inventory records 472 checkout-resolved sources and 63
unresolved imports, mostly Mathlib; it is not a clean rebuild. Existing NUC
manifests show cached provenance, not independently rebuilt first-party
artifacts.

No wire, protocol, transcript, acceptance, CU or Devnet change was made. No
global security claim is supported by this task.

## Remaining obligation DAG

```text
literal body + statement/context + legal causal prefixes
 -> source parser/transcript/semantic construction
 -> same-body Program and callbacks
 -> functional authentication/opening run
 -> SuccessfulAt / ideal execution or charged authentication failure
 -> allowed-access checked payment extractor
 -> raw and Fiat-Shamir composition, full-view ZK
```

Only the fixed-field arrow is newly closed. The next task is a
source-shaped `verify_relation` execution record that derives the outer
semantic functional/claim from the selected semantic verifier and constructs
callbacks at their actual prefix cuts. It must not take a Program or coherence
certificate as an unexplained input.
