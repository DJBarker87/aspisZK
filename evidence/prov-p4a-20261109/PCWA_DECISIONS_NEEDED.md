# PCWA_ decisions needed (lead)

Target not yet established. Nothing below changes a ledger row, trust row, RSL, the security contract or shipped source.

## D1. values_owned_reference (S1ValuesOwnedModelV1): source NOT found; lead decision packet

Gate module `S1ValuesOwnedModelV1` (evidence/port17release-20261024/dependency-source/S1ValuesOwnedModelV1.lean, sha256 4eacd73f095f07680d5fbba22b5ff8e1cf10429e46f454afb2f7891c541ac903; crate `aspis_s1_y1_source_20261024`, namespace `AspisS1ValuesOwned`; 8 reached definitions; 7 CLOSED rows: TX1:098, 151, 152, 168, 169, 170, 186; `copy_chunk*` is P4b's).

Search performed (all on `research`, whole tree): `git grep` for `fn values_owned_reference`, `values_owned_reference_loop`, `fn write_output`, `fn copy_chunk`, `aspis_s1_y1_source_20261024`; all 529 committed LLBC containers decoded and every embedded `translated.files[].contents` indexed (crate names, fn names) in this job (no embedded source defines `values_owned_reference`, `read_input`, `copy_chunk` or belongs to crate `aspis_s1_y1_source_20261024`); NML_INPUT_MAP.json group NMH_G059 (NO_HASH_LINKED_RECEIPT_FOUND); no extraction receipt/pins file records the Aeneas outputs of this module. The only trace is the Lean file itself: `Source: 'src/lib.rs', lines 31:0-34:1 ... 53:0-66:1` (spans of read_input, write_output, copy_chunk, values_owned_reference and their loops).

Two options, not chosen:

- (R) Reconstruct the reference from the Kani harness's recorded contract and re-run that Kani harness. Cost: identify the harness that binds `values_owned_reference` to the frozen function (not located by name in this job; unverified guess: tools/s8-kani-20261021/contract-kit), write the Rust reference (about 36 lines, fully determined by the emitted Lean spans), one extraction scope plus one Lean equality scope on this lane's tooling, and a Kani run on the build host (not allowed in P4a; for scale, NDL_K033 reports 19.8 s verification time while S8 harnesses kani-02/03/07/09 exit 124). Strength: restores a source, a Kani tie and a hash.
- (F) Re-route the consuming bridge to a P1 frozen emission. Cost: P1 extraction of the frozen `check_values`-side function that the 7 rows actually consume, plus re-proving the bridge against that emission instead of the reference model; no Kani. Strength: removes the reference from the trust path; the reference-to-frozen tie is no longer needed. Risk: the bridge theorem statement changes (different carrier), so rows TX1:098/151/152/168/169/170/186 would need the instantiation redone.

Noted but not a third option: because the Lean text carries exact Source spans, a reconstructed source can be validated by a byte-identical re-extraction (as done here for S8 and the neg_isolated crates). That proves the emission is reproducible from SOME source, not that the source is the historical one nor that the Kani contract applies to it.

## D2. NHI_GroupTablesExtracted, NHI_PartialIndexExtracted (not done, no decision needed)

Group d (no CLOSED root reaches them). Sources are in committed LLBCs (NHI_E002.llbc sha of src/lib.rs 92eb6572..., NHI_E003.llbc 083055991c3d...). Not extracted: the 12 extraction scopes were spent on relied modules. Cost if wanted: 2 extraction scopes, 1 Lean scope.

## D3. NHJ_SnapshotReference.Funs: two commented obligations (P3)

`ProgramError.Insts.CoreCloneClone.clone` and `snapshot_ref` need a transport between the fresh inductive ProgramError and the gate alias `abbrev ProgramError := NGL_MetaReference.ProgramError` (constructor names are not reachable through the alias). Statements are in eq/PRVEq_NHJ_SnapshotReference_Funs.lean (PRV-OBLIGATION blocks). Rows TX1:343, TX2:239 stay conditional until a P3 transport lands.
