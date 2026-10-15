# Current R1 semantic arithmetic coverage map

Read-only inventory from `/Users/dominic/ZK/.worktrees/100bit-spend-path`.
Current worktree source pins:

| Source | SHA-256 |
| --- | --- |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-core/src/field.rs` | `28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea` |
| `crates/aspis-core/src/field/wide_exact.rs` | `6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b` |
| `crates/aspis-core/src/state_only_hiding.rs` | `cc1039531cfe07518542d386668e9572e3eacf5127e8ec441c32bec20d116cd2` |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs` | `2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074` |

## Arithmetic call sites on `verify_observed`

`r1_semantic.rs:79–99` parses row 14 into `running`, initializes ten QM31 `alpha`
slots to `QM31::ZERO`, then loops rounds 0–9. Each round parses 28 QM31
coefficients from row 15+round. The boundary is a forward `fold` initialized
with coefficient zero and adds the other 27 values (`:86`); it is compared to
`running` (`:87–89`). The reader returns one semantic challenge and Horner
evaluation uses a reverse iterator fold initialized at `QM31::ZERO`, with
one `a.mul(alpha[round]).add(c)` for each of the 28 coefficients (`:90–99`).
The result becomes the next `running` value. Direct arithmetic here is QM31
addition and multiplication; `ZERO` is the sole direct field constant in this
loop.

After the ten rounds, claims are parsed and
`Public::terminal_qm31(&claims, &alpha, &original_challenges)` is called
(`:102–113`). Then `state_only_selected_mask_value` consumes row-25 claims,
`alpha`, and the explicit mask fields (`:115–120`). The final field equation is
`mask + eta * terminal + extra[28]` (`:121–124`), compared against the Horner
result. Equal circle points are rejected later (`:152–154`). `verify_observed`
has no direct `double`, `neg`, `from_u32`, `inv`, or `try_inv` call.

The current parser entrypoints are also relevant: `r1_semantic::decode`
requires a multiple of 32 bytes (`:25–30`), rejects nonzero bytes 16–31 for
each word (`:31–35`), and parses the lower 16 bytes through
`QM31::from_le_bytes` (`:36`). The protocol's `ValidatedRecord::decode_k`
performs the corresponding validated-record row decoding in `r1_wire.rs:134–158`.
At `field.rs:239–246`, M31 parsing is little-endian and accepts iff the
decoded `u32` is below P. CM31 parsing splits 8 bytes into two 4-byte M31
values (`:410–422`); QM31 parsing splits 16 bytes into two 8-byte CM31 values
(`:1022–1025`). These parser calls deliver canonical limb values if they
succeed, according to the retained parser lemmas below.

`terminal_qm31` delegates to `terminal_parts` in
`pair_forest_semantic_terminal.rs:2044–2062` and `:1285–1309`; the latter calls
`composition_parts` and forms an equality-weighted composition plus mu terms.
The selected-mask implementation is `state_only_selected_mask_value`
(`state_only_hiding.rs:647–675`): it constructs coefficient arrays, uses a
prepared QM31 multiplier in its Horner-like loop, adds the explicit-G factor,
and applies `mul_tower_basis` / `mul_by_r` helpers. Those helpers use M31/CM31
`neg`, `double`, `sub`, and `add` (`state_only_hiding.rs:436–464`). `terminal()`
also contains denominator inversions for wide interpolation
(`pair_forest_semantic_terminal.rs:2073–2100`), but the current semantic
verifier calls `terminal_qm31`, not that interpolation method; the inversion
at `:2097` is outside the observed call path. This identifies call sites only.

## Existing extracted-operation interfaces

Current Lean sources in `lean/` provide source-extracted contracts against the
actual Aeneas-generated field module:

| Lean file / declaration | Current contract exposed | Limitation for the verifier path |
| --- | --- | --- |
| `ExtractedCurrentM31AddSub.lean`: `current_add_mod`, `current_sub_mod` | On canonical M31 inputs, the extracted current `M31.add/sub` returns `.ok` with the stated modular value and canonical result. | Does not cover M31 `mul` here; multiplication is in the reducer module. It is a scalar operation contract, not a source verifier refinement. |
| `ExtractedCurrentReducer.lean`: `current_mul_mod`, `current_wrapper_mod` | Extracted current M31 multiplication/reducer result and canonical modular value. | No accumulated-call theorem for Horner or terminal acceptance. |
| `ExtractedCurrentTowerAdd.lean`: `current_cm_add_mod`, `current_cm_sub_mod`, `current_qm_add_mod` | Componentwise tower add/sub words over canonical inputs. | No whole-verifier execution equation. |
| `ExtractedCurrentCM31Mul.lean`: `current_mul_words`, `generated_mul_graph`, `generatedCrossFragment_success` | Current extracted CM31 multiply graph and exact word formula under canonical limbs. | Does not account for fast/prepared batched kernels in the selected mask implementation. |
| `ExtractedCurrentQM31Mul.lean`: `current_qm_mul_words` | Current extracted QM31 multiply result and `qmMulWords` formula under `CanonicalQM`. | No QM31 subtract theorem is exported in this module, no evaluator/loop composition, and no linkage to `r1_semantic.rs` call sites. |

These files have public `#print axioms` commands. Root has reported the focused
arithmetic targets green with standard Lean axioms; the present inventory did
not re-run builds or independently audit those receipts. `current_qm_mul_words`
does not by itself cover the optimized `PreparedQm31Multiplier` path used in
the mask code.

## Parser/canonicality reuse from the retained R12 proof batch

`evidence/lean-candidate-field-parsers-20261014/source-manifest.json` records
the seven-target parser bundle at source base
`6e25cda9d35e52df0980dbcd6744522bd3caaab0`. It retains
`CandidateFieldCanonicality` (`source_qm31_success_canonical` and
`source_cm31_success_canonical`), whose premise is successful parse of every
fixed-width byte array, not a canonical-input premise. Its dependencies include
`CandidateQM31Parser.from_le_bytes_refines`, `CandidateCM31Parser.from_le_bytes_refines`,
and `CandidateParserSupport.m31_from_le_bytes_eq_extracted`. The manifest also
pins generated Aeneas `Funs.lean` (SHA-256
`88817c538f86763ef18e8c09d2c68cbd1bdb673a63ba60da34b93bb52f15c776`) and
records only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
This route concerns the strict field parser and coordinate canonicality; it
does not prove the semantic verifier's arithmetic.

The same proof worktree contains `UnrolledWideParserRefinement.lean`
(SHA-256 `e057b44f28ffb7b398c9439c6945ce7ab05537053f956dd4c70b28016cc00aa6`)
with `source_refines`, `total`, `slice_success_canonical`, and `fixed_success`.
Those contracts refine the retained unrolled 32-byte WideExact parser to the
strict wide decoder and successful encoding reconstruction, using the
candidate QM31 canonicality result. This supports strict parsing of the wide
opening fields; it does not relate them to the QM31 scalar operations in the
ten-round semantic verifier.

## Explicit remaining coverage gaps

1. No retained theorem composes the per-operation arithmetic contracts over
   the source-shaped 28-coefficient boundary fold and 28-step Horner loop.
2. No checked relation currently connects `terminal_qm31` / `composition_parts`
   or `state_only_selected_mask_value` (including the prepared multiplier,
   tower-basis transforms, and full mask coefficient schedule) to a Lean
   `sumcheckChecksZ` predicate or the current selected verifier acceptance.
3. The existing parser canonicality results justify successful decode values;
   they do not prove byte-level verifier acceptance, challenge transcript
   behavior, or that the parsed values are the values consumed by a Lean
   semantic model.
4. `double`, `neg`, M31-to-CM31/QM31 lifts, `mul_m31`, prepared multiplication,
   and any relevant optimized formulas need their own exact extracted contracts
   or composition arguments where they occur. `from_u32` is not a direct
   operation in `r1_semantic.rs`; current semantic code constructs small M31
   constants inside the statement/mask helpers. No inverse appears in the
   `terminal_qm31` execution path described above.

This is an interface inventory, not a source-refinement, acceptance, or
security conclusion.
