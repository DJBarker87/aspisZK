# J1 relation reuse inventory (2026-10-15)

This is a source inventory, not a relation refinement or security result. The
lead decision in `design/LEAD-DECISIONS-20261015.md` calls for an executable
spend relation; the files below provide reusable specifications and checkers
at different layers, with a material gap between them.

## Existing R0 proposition and witness

`R0P.SemSource.Context` stores `pub : Public K` and 29 committed words;
`R0P.SemSource.paymentWitness x t` is exactly
`R0P.InputNoteExtracted x.pub t` (`v8-r0-sem-proof-20261008/lean/R0P/SemSource.lean:26-34`).
`R0C.SemStatement.SourceData.paymentWitness : X → W → Prop` is an arbitrary
proposition-valued callback, and `R0P.SemSource` supplies this instance. Its
`doomed`/`extract` use existential membership; `extract` chooses a witness
with `Classical.choose` (`v8-r0-close-20261007/lean/R0C/SemStatement.lean:45-56,99-109`).
Thus this is the R0 payment-witness interface, not an executable checker.

`R0P.InputNoteExtracted pub A : Prop` existentially carries `sk`, `salt`, and
`path : Fin 24 → Bool × Digest K`. It asserts the public nullifier is derived
from the key and salt and the public anchor equals a Merkle root of the input
note commitment at `A 10 1008` (`R0P/Semantics.lean:73-80`).
`input_note_extracted` proves it from six trace/copy premises:
schedule, path, digest, asset and Poseidon-scalar family `Holds`, plus
`CopyLinkBalance` (`R0P/Extraction.lean:328-349`). The trace witness names are
`traceSk`, `traceSalt`, and `tracePath` (`Semantics.lean:84-96`); `tracePath`
is `noncomputable` because it branches on a trace field using classical
decidability. The added `input_note_trace_witness` gives the same extracted
nullifier/root and a note-commitment equality (`Extraction.lean:351-360`).
`SemAssembly.extraction_step` is the existing wrapper from
`ProductionHolds ∧ CopyLinkBalance` to `InputNoteExtracted`
(`R0P/SemAssembly.lean:76-89`).

The R0 public carrier is `Variant ×` fields including
`recipient : Option (Digest K)` and `withdrawalAmount : Option K`
(`R0P/Core.lean:50-67`). The carrier itself has no canonical-option-shape
predicate. `SpendSemantics.NoteFacts` is a useful but partial Prop: bounded
balanced values, extracted input, change commitment, and conditional
recipient/withdrawal bindings (`lean/SpendSemantics.lean:13-26`). Its own
comment excludes append update and public `Option` shape; conditional clauses
do not require the appropriate option to be present or forbid the other one.
`SpendExtraction.large_matching_extracts` produces `NoteFacts` under its
semantic/opening/matching premises, not the full payment relation
(`lean/SpendExtraction.lean:37-68`).

## Existing executable Rust relation and Pair Forest path

`payment_relation.rs` is explicitly documented as an executable, no-proof
semantic foundation. It defines separate transfer/withdrawal public structs,
input/output witness structs and a runtime-binding context
(`crates/aspis-statement/src/pool_v1/payment_relation.rs:45-125`). The input
witness is `(nullifier_key, salt, value, siblings[depth], index)`; each output
witness is `(owner_key, salt, value)`.

The public format checkers are `validate_pool_v1_private_transfer_public_v1`
and `validate_pool_v1_withdrawal_public_v1`, both returning
`Result<(), PoolV1PaymentStatementFormatError>` rather than Lean propositions
or Rust `bool` (`payment_relation.rs:182-246`). They check nonzero pool/domain,
anchor sequence bound, canonical digest limbs and M31 asset; transfer checks
recipient/change digest canonicality; withdrawal checks `0 < amount < limit`,
nonzero destination and change digest canonicality. The corresponding
`decode_pool_v1_*_public_v1` functions validate exact fixed-width headers and
canonical fields (`payment_relation.rs:314-449`). The two Rust public types
encode the variant shape in their type: transfer has a recipient commitment
and no withdrawal amount; withdrawal has amount/destination and no recipient
field. This differs from the unconstrained R0 `Option` carrier.

`pool_v1_membership_root_v1` checks the index is below capacity and folds the
siblings using successive index bits (`payment_relation.rs:504-520`).
`validate_common_relation` binds the statement to runtime pool, deployment,
sequence, root and asset; recomputes input note root and nullifier; and rejects
already-spent nullifiers (`:537-573`). The public evaluators
`evaluate_pool_v1_private_transfer_v1` / `evaluate_pool_v1_withdrawal_v1`
check witness digest canonicality, value ranges and conservation, input
membership/nullifier, and output commitment(s), returning `Result<(),
PoolV1PaymentRelationError>` (`:575-657`). This is the clearest existing
executable full payment-relation checker in this source tree; no Lean theorem
currently identifies it with `InputNoteExtracted` or `NoteFacts`.

The pair-forest trace path independently constructs the algebraic trace from
the membership index/siblings and checks the reconstructed anchor
(`pair_forest_trace.rs:55-109,200-264,322-369`; payment trace checks
conservation and commitments at `payment_trace.rs:383-465`). The selected
terminal is a scalar constraint-composition evaluator, not the full payment
checker: the exported functions evaluate selected composition/unmasked/masked
terminal values (`pair_forest_semantic_terminal.rs:1348-1439`). Its private
`validate_transition` checks append-frontier shape and permits index
`POOL_V1_PAIR_CAPACITY - 1` (`:180-208`). The Pair Forest semantic-public
conversion fixes transfer to `recipient=Some(..), withdrawal_amount=None`
and withdrawal to `recipient=None, withdrawal_amount=Some(..)` (`:1312-1345`);
these are constructors, not an R0 theorem or a general public decoder.

The legacy depth-20 payment-membership evaluator and its residual checks are
not the current full payment relation. The R0 input witness instead carries a
24-level path (`Fin 24`). The current Pair Forest semantic-terminal entrypoint
is a separate evaluator; no direct or transitive call from that entrypoint to
`pair_constraint_residuals` or `pair_forest_constraint_residuals` was found.
See `APPEND-REUSE-NEXT.md` for the entrypoint/call-graph split and exact
source pins.

## Reuse boundary and known representation gaps

- Reuse the R0 existential interface and `input_note_extracted` when the
  target is specifically the abstract trace statement. The theorem's path is
  24 levels (`Fin 24`), whereas the Pool V1 runtime membership witness uses
  `POOL_V1_TREE_DEPTH` siblings (asserted as 20 in
  `payment_trace.rs:77`). No correspondence proof bridges these paths here.
- Reuse `SpendSemantics.NoteFacts` for its existing abstract value/input/output
  facts only. It is not a decidable checker, does not impose canonical
  public-option shape, and its input commitment/value coordinates are R0 trace
  coordinates.
- Reuse the Rust `evaluate_pool_v1_*_v1` functions as executable checkers at
  their stated runtime-binding context. No Lean refinement connects their
  `Result` behavior, Rust byte parser, Pair Forest trace compiler, or selected
  terminal to the R0 `paymentWitness` proposition.
- There is no current single witness type or theorem composing the R0
  candidate trace with Rust `PoolV1*WitnessV1`, public encoding/canonicality,
  bounded integer conservation, output commitments and runtime freshness.

## Source pins

All hashes below are SHA-256 of the exact files in this worktree.

| File | SHA-256 |
|---|---|
| `design/LEAD-DECISIONS-20261015.md` | `46a6502de8deafae774a62a589c91dcfbe0791e186e8db36651078b80c81c8e4` |
| `lean/SpendSemantics.lean` | `a81f79a0401980cf22b448988eb1ddf0a2d5ae571d38bb85fc45908919a7774d` |
| `lean/SpendExtraction.lean` | `b1ab643fddcc1ddd4be5e5efa9c7d7291c0067feb9214b2d4bc76a8d8b66a523` |
| `v8-r0-sem-proof-20261008/lean/R0P/Core.lean` | `eba6bb784803b5f00922724efc9997a8d5ab6bc55cd8c100bffd8a397dabe1f9` |
| `v8-r0-sem-proof-20261008/lean/R0P/Semantics.lean` | `9309c5faa3de30d4f35bfe46509fe335a821d89a43051201a97232c0b89dc615` |
| `v8-r0-sem-proof-20261008/lean/R0P/SemSource.lean` | `e79ce46d3ce2dc99e65aa99c78581f5069c66eec3dba4dae0dce09ec86f7a024` |
| `v8-r0-sem-proof-20261008/lean/R0P/Extraction.lean` | `7f7736179026639936fa5d7ad1647e9804676863cf328cb416ea8723d2b72804` |
| `v8-r0-sem-proof-20261008/lean/R0P/SemAssembly.lean` | `7ef49bd9a94338bc5b8aeda48fa08f415bdb57cf14bd483e4475ceff0b6c17fc` |
| `v8-r0-close-20261007/lean/R0C/SemStatement.lean` | `065e73821e28582b1e08073fb64383f0bec7342cf8fed0cbbe3bd68430fab90d` |
| `crates/aspis-statement/src/pool_v1/payment_relation.rs` | `8b543d3de5aa29d1e510e8ca18bd2bc6dae6c405b7d6f97402c572dfdbab2588` |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs` | `2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074` |
| `crates/aspis-statement/src/pool_v1/payment_trace.rs` | `8dba76d6fe6f19d2b800118855612e4dde1e5ef9869d14df2fbd96861dc288d2` |
| `crates/aspis-statement/src/pool_v1/pair_forest_trace.rs` | `0a97cbba7740acf44e3b85082ff917e6fb60b81a26662a2d7f96acaf0e72309d` |
| `lean/C1PartialCandidates.lean` | `1ca6a34a91d5565cd0b19100cead2353d6d365c2dd5f49fa6c8ecd668a3cf1ae` |
| `lean/IncrementalCandidateLoop.lean` | `3304883df4d6802726fa65ba5a5a27a12e3cd18806db680c6b5cf6c3a61c9524` |
| `lean/TypedRecoveredWords.lean` | `85243ca24d3e9fc6272847244b77796cd3f7ea98397fc563783a212c6b8e1350` |
| `lean/SemanticRecordCodec.lean` | `5cf8fb6510c397d5d3c505b72bc24a5b2f4079ccb5a9e74e0c2eed14229bcbd3` |
