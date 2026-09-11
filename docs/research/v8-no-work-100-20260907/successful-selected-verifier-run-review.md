# Successful parsed selected field run constructs an ideal execution

Status: focused Lean result at the compact-field verifier boundary.
Research parent: `eb06c838bdeb002508dac2b4af406631f3d67e66`.

The retained theorem is
`successful_selected_verifier_run_constructs_ideal_execution` in
`experiments/SuccessfulSelectedVerifierRun.lean`. It is the first umbrella
consumer in this continuation: a successful causal run with canonical proof
bodies constructs the same `CausalCoveredRecovery.Execution`, proves its ideal
terminal acceptance, supplies the unique complete accepted-prefix partition,
and constructs the fixed residual-recovery classifier for that execution.

## What is constructed rather than assumed

- Each response callback returns bytes at its actual causal boundary. Gamma
  and kappa precede all five callbacks; final256 may depend on alpha0; query
  responses have precisely the queries/rho/previous-alpha dependencies that
  precede them.
- `CanonicalRelationInput.parseFixed` parses every actual-path body. The
  theorem carries all five 697-field length facts; malformed or noncanonical
  bodies cannot reach this successful event through a default field vector.
- `TypedRelationTerminal.Decoded.fields` constructs the strategy from those
  decoded response0/final/response1/response2/response3 values. There is no
  premise equating a separately supplied ideal strategy to a source strategy.
- The C1 received word is `fixedC1 earlyRecords c1Root`. The root is tied to
  bytes 11152..11177 of every actual-path body by `ParsedAt`; changing a root
  byte while retaining the old C1 now falsifies the success predicate.
- `callback_accepts_iff` transports the source-shaped compact terminal into
  the exact ideal `accepts` event. `accepted_partition` then covers every
  accepted branch, including no-good/provider-none branches.
- `exists_source_classifier` constructs E, the at-most-one fixed tuple family,
  the at-most-28 sparse-gamma set, and the OOD-dependent beta plan from this
  execution's actual C1/C2 parent. It does not assume candidate membership.

The selected nonzero gamma, kappa, tau and rho premises are all retained.
They are properties of this ideal successful path; this leaf does not yet
prove that Fiat-Shamir sampling supplies their laws.

## Exact boundary—not yet Rust or a checked payment witness

This theorem is deliberately narrower than
`performance_verifier::verify_parsed(body) = Ok(()) -> ...`.

| Connected here | Still required for the actual selected verifier |
| --- | --- |
| Canonical 697-field parsing and compact response/final offsets | One complete Wire parser tying all fixed fields, both roots, query records and frontiers to one proof body/history |
| Causal decoded callback strategy | Rust/Aeneas refinement of the selected callback and terminal |
| C1 root bytes to the early-prefix total word | Accepted-opening projection for all used C1 values, or charged late-target/raw-collision alternatives |
| Explicit total C2 word | C2 root/opening authentication and its lambda/chi fixing boundary |
| Typed OOD data, weights and claims | Exact fixed-field offsets and source construction of these values |
| Ideal query schedule and received oracle | Packed query parsing, Merkle verification and equality of disclosed values to that oracle |
| Complete ideal accepted-prefix partition and classifier | Residual theorem composition to an efficiently checked payment witness |

This separation is forced by a concrete regression: parsing only the first
697 fields ignores a mutation at byte 11152, while the Rust verifier uses that
byte as the C1 root. The new `bodyC1Root` equality closes that mutation inside
this field model. It does not by itself prove Merkle authentication or that
five causal completion bodies assemble to one noninteractive proof.

Thus the commit title says *parsed selected field run*, not *production Rust
verifier*. The next source theorem should construct `Program` and `SuccessfulAt`
from the actual selected Wire/opening checks; it must not add an equality
premise that simply restates the missing refinement.

## Security and cost effect

No new probability term is introduced and no local 110-bit bound is promoted.
The result consumes existing residual-recovery mathematics only after the
accepted execution has been constructed. Raw global knowledge soundness is
still conditional on the authentication/source and tuple-to-payment-witness
bridges above. Fiat-Shamir extraction and full-view zero knowledge remain
separate. No grinding credit is used.

The proof body remains exactly the accepted maximum model:

`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes`.

No verifier operation, proof byte, transcript message or production default
was changed. This formal bridge therefore supplies no new CU measurement and
does not establish complete-transaction parity.

## Focused evidence

The successful NUC run used Lean 4.32.0, `-j1 -M9500`, and one systemd scope
with MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0 and CPUQuota 200%.
It exited 0 in 3.12 s wall time, used peak RSS 6,892,064 KiB and reported zero
swaps. All three printed declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` appears.

Exact command, hashes and pinned import provenance are retained in:

- `experiments/successful-selected-verifier-run-v4.log`
- `experiments/successful-selected-verifier-run-v4-manifest.json`
- `experiments/successful-selected-verifier-run-v4-source.txt`

The two focused dependencies have separate retained v2/v4 evidence. No broad
manifest replay, generated-certificate aggregation or production build was
run. Concurrent NestedCircle/StoppedPrefix artifacts were not modified.
