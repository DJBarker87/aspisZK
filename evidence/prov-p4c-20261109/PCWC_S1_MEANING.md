# PCWC_S1_MEANING: what S1ValuesOwnedModelV1 stands for (items S1 and S2)

Target not yet established. Nothing here changes a ledger row, trust row, RSL, the security contract or shipped source.

## 1. Answer

`S1ValuesOwnedModelV1` (crate `aspis_s1_y1_source_20261024`, namespace `AspisS1ValuesOwned`, sha256 4eacd73f..., Types S1ValuesOwnedTypesV1 45615bdd...) is a **hand-written owned-buffer reference implementation of the frozen function `compact::expand_values`**, not an extraction of frozen code.

* Frozen counterpart: `crates/aspis-r1-cost-probe/src/compact.rs` at 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, `pub fn expand_values(compact: &[u8], out: &mut [u8]) -> Result<(), CodecError>`, starts at line 127 (doc comment 123-126; body ends with `Ok(())`, `}` at 136). Callers in the frozen tree: `candidate.rs:259` (`compact::expand_values(&proof[OFF_Y1..OFF_INACTIVE], y1)?`), `compact.rs:160` (`expand_semantic`).
* The frozen function checks `compact.len() % 16 == 0 && out.len() == 2*compact.len()` (else `CodecError::Length`) and, per 16-byte chunk, copies the chunk into `out[..16]` of the matching 32-byte cell and fills `out[16..]` with 0, via `chunks_exact(16).zip(chunks_exact_mut(32))`, `copy_from_slice`, `fill`.
* The reference does the same thing with byte indices over `Vec<u8>`: `values_owned_reference` (same two length checks, `CodecError.Length`), outer loop over `count = len/16` chunks, `copy_chunk` inner loop over 16 bytes through `read_input`/`write_output` (`out[32c+b] = in[16c+b]`, `out[32c+16+b] = 0`). It takes and returns owned `Vec<u8>` for both buffers (the frozen function borrows `&[u8]`/`&mut [u8]`); the Lean carrier `CodecError` is `AspisR1CurrentCaller.compact.CodecError` (Types module), the extraction of the frozen error type, so the status values are the frozen ones.
* So the module is a model *of a specific frozen function* (name above), written in a different style (index loop instead of iterator zip and slice copy/fill). The equivalence "reference = frozen `expand_values`" is **not proved in the repository by an Aeneas-level equality**. Its justification in the repository is two-fold and indirect: (a) the docstring of `AspisS1ValuesOwnedExact.installed_exact` says the reference "satisfies the SAME byte formula checked on the unchanged native function" (a Kani/other check of the frozen function against the byte formula `out[j] = if j%32<16 then in[(j/32)*16+j%32] else 0`), (b) the reference's own theorems prove that formula for the reference (`reference_bytes`, `accepted_bytes`). No Kani receipt naming this crate's source was found (PCWB D1, PCWA D1 searches; this job re-checked, see PCWC_S1_RECONSTRUCTION.json). The reference source file `src/lib.rs` is not in the repository.

## 2. Consumers of the 8 reached definitions

Reached definitions (16 constant names including auxiliaries, all in every reaching root's reach list): `read_input`, `write_output`, `copy_chunk`, `copy_chunk_loop`, `copy_chunk_loop.body`, `values_owned_reference`, `values_owned_reference_loop`, `values_owned_reference_loop.body`.

Direct consumers (sources: `evidence/port17release-20261024/dependency-source/` and, for the later modules, `evidence/replay-dry3-20261026/RPz2_recovered/`; the latter are recovered copies, so which text was compiled is the usual `compiled_source_ambiguous` caveat, the import graph in NNN_LOADED_scan.jsonl matches their imports):

| definition | consumed by |
|---|---|
| read_input | `AspisS1ValuesOwnedFrame.read_frame` (unfolds it); `copy_chunk_loop.body`; `AspisS1ValuesOwnedCell.read_exact` / `AspisS1ValuesOwnedTotal.read_spec` (specification of its result) |
| write_output | `AspisS1ValuesOwnedFrame.write_length`; `copy_chunk_loop.body`; `AspisS1ValuesOwnedCell.write_exact`/`write_byte`; `AspisS1ValuesOwnedTotal.write_spec` |
| copy_chunk, copy_chunk_loop, copy_chunk_loop.body | `AspisS1ValuesOwnedFrame.chunk_body_frame`, `chunk_frame`; `AspisS1ValuesOwnedChunkFormula.*`, `StepBytes.step_bytes`, `ChunkBytes.chunk_bytes`, `AspisS1ValuesOwnedTotal.chunk_step_total`, `chunk_loop_total`, `chunk_total`, `chunk_spec` |
| values_owned_reference_loop(.body) | `AspisS1ValuesOwnedFrame.outer_body_frame`, `outer_frame`; `AspisS1ValuesOwnedExpansionFormula.*`, `ExpansionBytes.step_bytes`, `loop_bytes`; `AspisS1ValuesOwnedTotal.outer_step_total` |
| values_owned_reference | `AspisS1ValuesOwnedFrame.reference_frame`; `AspisS1ValuesOwnedReferenceBytes.reference_bytes`; `AspisS1ValuesOwnedExact.reference_success`, `installed_exact`; `AspisS1ValuesOwnedInstallation.expandValues` (the only definition that calls it as a function), `length_frame`, `accepted_bytes` |

The interface to the rest of the proof is `AspisS1ValuesOwnedInstallation.expandValues` (Slice-to-Vec conversion `toVec`/`toSlice` around `values_owned_reference`), installed as the caller operation **`op11` of the current compact caller model** (`withValues ops := {ops with op11 := expandValues}`, `nativeValues := {expandValues := expandValues}`). `op11` is the position in `CurrentCompactCallerModelV1` that is applied to `proof[OFF_Y1..OFF_INACTIVE]` and `y1` in the prepare function (the call to `compact::expand_values` at candidate.rs:259). Theorems that carry it upward: `AspisS1ValuesOwnedInstallation.accepted_bytes`, `RPz7_S1ValuesOwnedPrepareViewY1V1.prepare_view_y1`, `RPz7_S1ValuesOwnedStage1RootsV1.owned_stage1_physical_roots`, `RPz7_S1ValuesOwnedStage1ViewY1V1.owned_stage1_view_y1` (these consume the installation with all pieces `withValues ops nativeValues`). Docstrings in those modules state: "Native/reference transport over the reached format domain and SDK/account correspondence remain separate obligations", i.e. the reference-to-frozen step is an explicit, still open obligation at that layer.

## 3. Consequence for provenance (no claim beyond this)

* The module has no extraction source and no hash-linked receipt (NMH G059 NOT_REPRODUCED). If S3 reproduces the Lean from a reconstructed crate, that shows the emission is reproducible from SOME source, not that it is the historical source.
* The obligation that matters for the 7 rows is the equality of this reference with frozen `compact::expand_values` (stated in PCWC_S1_OBLIGATION.lean). It is a P3 obligation, not attempted here.
