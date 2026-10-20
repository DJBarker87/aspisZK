# Finish field-selector canonicality bridge

This focused Lean owner proves that a successful invocation of the retained generic `weights.field` selector, instantiated with the retained record parser's `WideExact.from_le_bytes`, maps to a `FinishE` value satisfying `CanonicalFinish`. The map preserves all eight `U32` limbs; the parser and Finish M31 declarations are both aliases of `Std.U32`.

The proof obtains the selected byte slice through `WeightsFieldSuccess.checked_slice_decode`, then applies `ExtractedRecordByteCanonicality.slice_success` to get the eight canonical limb bounds. It deliberately avoids the Stage2 generated `verifier.Error` owner that collided with Finish's generated Error instance.

Target: `FinishFieldSelectorAdapterV2` (`/tmp/FinishFieldSelectorAdapterV2.lean` at run time; frozen copy is in `sources/`). Source SHA-256: `5249244624c5d79e570c52a29030a9b8dc773b150063e915c523cd309d121364`. Object SHA-256: `c7ed8358d4c8e583aa1df9f4e612e3928eab210340d651eed63f087ed086126f` (object intentionally excluded from this source-only packet). NUC receipt: exit 0, 2.107 s, cgroup peak 373,280,768 bytes, swap 0. Both new theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

Direct imported object pins are recorded in `evidence/preflight.json`: `CurrentFinishArithmetic` 5edd21dfc6f56ebea717c5b2ee0c290c1c988b261c44d0f4faa91ae7b76ccaf6; `WeightsFieldSuccess` 988b67e4c1b59ffdcd168ff3383645fdef6614b1650e09a476903949990dcd48; `ExtractedRecordByteCanonicality` 1f7406232cab30165799f257dac60b50074ca353300147c23fb1639200404419. Compiler is Lean 4.32.0, SHA e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550. The exact run configuration, admission/reservation metadata, command, Lean log and GNU time log are included.

Scope limit: this proves the parser-backed selector adapter. It does not prove the Stage2 Reader nominal conversion or the complete Finish relation/caller theorem; the consumer can use `record_field_finish_canonical` to discharge the field-canonicality obligations once its selector is connected to this exact parser-backed call.


## Rust parser source lineage

`lineage/check-lineage.py` compares packet-local source files. It checks the exact `WideExact::from_le_bytes` method span against current Rust source, the frozen c8 source snapshot, and the record-parser extraction fixture. All three method spans are 1,079 bytes with SHA-256 `0e5c8f656afd474c7627ce0583343ee9a84d77cc444a326ad1ffb70726a43048`. It also checks that the generated RecordParser and ViewParse Lean function bodies are identical. The checker is a literal source/body comparison and does not prove Aeneas translation correctness. The included RecordParser receipts identify the generated owner and its source manifest; the V11 Lean theorem consumes that owner.

Current and frozen c8 full `wide_exact.rs` SHA-256: `6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b`; frozen c8 revision: `c8ea8dd49c81ab970b9dbee8d8b47718f9beb005`. Record-parser Funs SHA-256: `f6a3d5b95b781458af5a0118b76d39a14243b77958ef86eb9e5cac50ac45a2b1`.
