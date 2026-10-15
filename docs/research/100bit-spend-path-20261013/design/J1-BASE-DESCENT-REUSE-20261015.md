# J1 base-field descent reuse inventory

Source inspection only, at repository revision `c7b5a949e2274b15ac91a6299fbbc3da691aeb3c`. This records existing theorem links and representation boundaries; it does not establish a Rust refinement, a J1 extraction theorem, or a security conclusion.

## Reusable descent chain

The direct candidate route is already present in `lean/CandidateDescent.lean` (SHA-256 `864981f4ed16c09db4a2a5752979d94c4c9ddbb53471fe9f83a58994c9b9367f`). `WordTyped S W` means every committed initial-codeword coordinate `W l i` belongs to lane subfield `S l`. Given that typing and `t ∈ ConcreteBinding.candidates W`, `candidate_codeword_typed` proves `exactInitialEncoder (t l) i ∈ S l`; it uses the existing agreement threshold and `initialCodeword_subfield_descent`. `candidate_message_typed` then proves `MessageTyped S t`, i.e. every coefficient `t l r ∈ S l`, through `initialMessage_subfield_descent`. `candidate_rows_typed` gives the exact reindexed result `t l (π r) ∈ S l` for any equivalence `π : Fin 1024 ≃ Fin 1024`.

The row transport already used by the semantic bridge is `R0P.SemSource.rowsOf` in `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemView.lean:35` (SHA-256 `a8e8fab6e0efaa76bf64f1197edb5ab51327f8906aecdb668c55885e94837fbd`): `rowsOf π m c r = m c (π r)`. Its inverse/coefficient conversion is `coeffsOf` at line 32, with `rowsOf_coeffsOf` and `coeffsOf_rowsOf` at lines 38–46. R1's `rowEquiv` in `lean/D18Transport.lean:166–170` is an involutive equivalence on `Fin 1024`, not identity. Thus the relevant trace fact is about `rowsOf rowEquiv t`; it is not obtained by treating coefficients and trace rows as identically indexed.

There is an already-composed witness route in `lean/SemanticTransport.lean` (SHA-256 `8798a2a6ff2a78dd4f0ccfe034ae4e4da9bd2aefe4566d2fd7b4fdbf9ece8886`): `witness_baseTyped` at lines 66–81 gets `SemanticOpening.witness_rows_typed`, uses `rowsOf rowEquiv`, and returns `R0P.BaseTyped F ...`. Its lane-uniformity premise is `lanesF : ∀ l, l.val < 26 → S l = F`. `SemanticOpening.Witness` contributes more than candidate membership: it also carries the point/extra claims. For the narrower descent statement, `CandidateDescent.candidate_rows_typed` is the direct reusable theorem.

## Matching the recovered-word lane

`lean/TypedRecoveredWords.lean` (SHA-256 `85243ca24d3e9fc6272847244b77796cd3f7ea98397fc563783a212c6b8e1350`) defines `laneSubfield eM eK l` at lines 45–47: use `eM.fieldRange` when `l.val < 26`, otherwise `eK.fieldRange`. `word_typed` at lines 63–73 proves the decoded `word eM eK c1Packed c2Packed` is `CandidateDescent.WordTyped` by `RingHom.mem_fieldRange_self`. Here the selected base embedding is `ExactBaseProjection.embed : M31Exact →+* WideExact`, composed from the exact tower algebra maps, in `lean/ExactBaseProjection.lean:14–18` (SHA-256 `762d9cea59495ee9f227c2df2c0c8ec4182ea0f8f46bc714d351a2228eb31cec`). `project_embed` and `embed_project_of_mem_fieldRange` at lines 23–32 show the coordinate projection is a left inverse on embedded values and recovers any value already in that range. The projection is not claimed to preserve operations on arbitrary wide-field values.

Consequently, with `W := TypedRecoveredWords.word ExactBaseProjection.embed eK ...`, `CandidateDescent.candidate_rows_typed` at `π := rowEquiv` yields, for every `c : Fin 16` and `r : Fin 1024`, `(R0P.SemSource.rowsOf rowEquiv t) c r ∈ ExactBaseProjection.embed.fieldRange`: `c.val < 26`, so the lane subfield is exactly the base embedding's field range. The stronger existing `SemanticTransport.witness_baseTyped` states this uniformly for all `c < 26`. This is the precise bridge from a *typed recovered codeword plus candidate membership* to base-field semantic trace cells. `candidate_codeword_typed` alone is not enough to conclude coefficient/trace typing; the coefficient step is `candidate_message_typed`.

## Relation-cell locations and limits

The physical trace is `R0P.Trace K := Fin 29 → Fin 1024 → K` (`lean/R0P/Core.lean:20`, SHA-256 `eba6bb784803b5f00922724efc9997a8d5ab6bc55cd8c100bffd8a397dabe1f9`). The adjacent source comment at lines 27–29 calls columns 0–15 semantic C1, 16–25 mask-only C1, 26 H1, 27 G, and 28 D; `rowOpenings` at `docs/research/v8-r0-sem-proof-20261008/lean/R0P/Core.lean` uses only the first 16 columns.

The current abstract input relation is `InputWitnessCore.Relation` (`lean/InputWitnessCore.lean:13–22`, SHA-256 `fec688b4ae7650f4ba4c266613853eb9f858aabd5d36f2d8a5f4d01107a85d5d`). The pair comes from `InputPair.leaf` (`lean/InputPair.lean:14–18`, SHA-256 `e97853456b75cc9970db0504df22b398802cc81d03993d492eec59f2d348316e`): second occupancy/inverse are columns 0/1 at row 1017; second commitment limbs are columns 2–9 at row 1017; the first commitment is `AppendNode.left A 4`. `InputPairSelection.path_bit` uses column 0, row 913; `left_path`/`right_path` read the two eight-lane siblings from columns 0–7/8–15 at row 914 (`lean/InputPairSelection.lean:12–29`, SHA-256 `7c0aa7bc71afe9d6b2e4ff8c59847dad28f76529d7d5682ac8f8d1c479400f45`). `selected_output` binds the chosen pair commitment to `OutputNotes.output A 3` at lines 31–56.

`R0P.Semantics.lean:73–96` (SHA-256 `9309c5faa3de30d4f35bfe46509fe335a821d89a43051201a97232c0b89dc615`) defines `traceSk` at column 0–7, row 12; `traceSalt` at columns 2–7, row 44 and 0–1, row 60; and path bits at column 0 with sibling digests in columns 0–7 or 8–15 at the next row. The input value is `A 10 1008`. Output-note chunks and outputs are `digestOf (poseidonState A block 12)` and `digestOf (poseidonState A block 11)` in `lean/OutputNotes.lean:17–21`; `poseidonState` is defined in `docs/research/v8-r0-sem-proof-20261008/lean/R0P/Poseidon.lean:396` by selecting `A (lane.castAdd 13)` at the scheduled row. These referenced trace coordinates all have lane/column below 16. This is a source/model location inventory, not a proof that an arbitrary parsed leaf or recovered word supplies those exact trace coordinates.

`SpendDataMap.witness_id` and `witness_comp` (`lean/SpendDataMap.lean`, SHA-256 `f1016a4bad5b6f7f8e1a917edfcf717889d8aff68b5a8ee0a374906fd701eb88`) are only structural map laws. The file deliberately does not state that arbitrary scalar maps preserve spend equations. `SpendRelationExtraction.of_production` provides an existential witness from production trace facts, but it does not connect a parser's recovered fields to that witness. `InputWitnessCore.Relation` also includes pair occupancy, pair/path links, nullifier, and membership equations; the base-typing theorems do not discharge any of them.

## Exact next bridge boundary

The available deterministic route can prove a theorem of this shape without an additional trace-field hypothesis:

```lean
let W := TypedRecoveredWords.word ExactBaseProjection.embed eK c1Packed c2Packed
let S := TypedRecoveredWords.laneSubfield ExactBaseProjection.embed eK
 t ∈ ConcreteBinding.candidates W
 → ∀ c : Fin 16, ∀ r : Fin 1024,
    (R0P.SemSource.rowsOf rowEquiv t) c r ∈ ExactBaseProjection.embed.fieldRange
```

It is just `CandidateDescent.candidate_rows_typed` plus `word_typed` and the lane bound `c.val < 26`. This leaves the substantive J1 connection explicit: a recovered/canonical input witness must be related to the candidate tuple (and relevant recovered word), and the M31-to-Wide map must preserve the particular relation equations used by the selected spend. No current theorem in `SpendDataMap` supplies that preservation, and no theorem here identifies parsed source bytes with the `InputWitnessCore.Relation` fields.

## Source pins

All paths above are relative to this repository. Hashes are listed inline for the modules most directly consumed; additional position-source pins are: `OutputNotes.lean` SHA-256 `70899b6106486fc78418509dae3c7c3ff378358bb19e2e21f9ad7ac9c91a4fa2`; `D18Transport.lean` SHA-256 `ffa944f42b5188e89d6a538a5fe345e4347a148dcc080feb01673c82b6099033`; `R0P/CoreExt.lean` SHA-256 `7b0a6820f1f6d446943447509edd40babf84801eb1f06aeabd868ff033d41188`.
