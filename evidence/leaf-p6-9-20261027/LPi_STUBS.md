# Stub obligations

A paired theorem must prove total success AND the same value predicate as the stub, on a domain established by the caller. A safety-only or conditional-success theorem is insufficient. Names below are in AspisR1 unless qualified.

| Operation | Domain | Emitted-definition value theorem | Current status |
|---|---|---|---|
| M31.mul | all two raw U32 | LPf_BaseMultiply.source: exact natural product mod 2147483647, canonical result | CLOSED Lean pairing; native/model association retained |
| CM31.mul | canonical two limbs per input | LPi_CMProduct.source, realWord/imagWord coordinate formulas | CLOSED Lean pairing |
| mul_by_r | canonical CM31 | LPi_FieldValues.by_r, cw/byR natural coordinates | CLOSED Lean pairing |
| QM31.mul | canonical four limbs per input | LPi_TowerValues.qm_mul, qw/mulQ natural coordinates | CLOSED Lean pairing |
| QM31.mul_m31 | four U32 and scalar | LPi_MixedValues.qm_m31: all four product residues | CLOSED Lean pairing |
| WideExact.mul | canonical eight limbs per input | LPi_TowerValues.wide_mul, ew/mulE natural coordinates | CLOSED Lean pairing |
| Q.raw | canonical four limbs per input | LPi_RawValues.source derives SAME total FIo raw return and exact repaired rawC0–3 | CLOSED Lean pairing |
| Q reduced product | canonical four limbs per input | LPi_RawResidue.source composes SAME raw return and actual Dot.finish residues | Pairing compile pending |
| CM31.write_le_bytes | arbitrary initial exact8-byte mutable slice, raw U32 limbs | LPi_WriterValues.cm_writer: output is cbytes = LE(a) ++ LE(b) | CLOSED Lean pairing; caller harness pending |
| QM31.write_le_bytes | arbitrary initial exact16-byte mutable slice, raw U32 limbs | LPi_WriterValues.qm_writer: output is CheckpointP6EncodeK.bytes | CLOSED Lean pairing; caller harness pending |
| E.to_le_bytes | canonical8 limbs | LPi_EWriter.source reuses unchanged emitted serializer and exact ordered8 LE word layout under explicit P6 model | CLOSED Lean value pairing; std/iterator ABI retained in D188 |

No unpaired stub is accepted as closure. Writers must constrain every written byte to the four-byte little-endian word layout and preserve all bytes outside their passed slice by Rust borrowing. A stronger whole-buffer frame needs caller-context checking.

FIo_FieldValues import exploration hit missing PAln_RowBounds/Port5Q1_Ten. LPi_missing.json is a SOURCE import inventory, not proof that all listed modules are absent from the actual object closure. No shared object was changed; direct natural coordinate laws avoid this unrelated closure. Failed axioms reports containing sorryAx are excluded.

M31.to_le_bytes is the literal emitted `ok (core.num.U32.to_le_bytes self)`; an explicit audited alias will precede any mbytes caller result. LPi_ByteWord.source audits the literal M31 byte result. Rust stubs in LPi_contracts.rs are currently unrun.

L016 was rejected by the unchanged runner before Lean launched because its direct prerequisite LPi_CMProduct had not yet compiled. This was a correct dependency preflight rejection, not a launcher repair. L017 supplies the missing object; L018 then reached elaboration. No admission rejection was bypassed.
