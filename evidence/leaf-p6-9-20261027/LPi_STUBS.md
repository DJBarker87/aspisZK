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
| Q reduced product (raw→Dot.finish) | canonical four limbs per input | LPi_RawResidue.source composes SAME raw return and actual Dot.finish residues | CLOSED Lean pairing |
| CM31.write_le_bytes | arbitrary initial exact8-byte mutable slice, raw U32 limbs | LPi_WriterValues.cm_writer: output is cbytes = LE(a) ++ LE(b) | CLOSED Lean pairing; native contexts pass (below) |
| QM31.write_le_bytes | arbitrary initial exact16-byte mutable slice, raw U32 limbs | LPi_WriterValues.qm_writer: output is CheckpointP6EncodeK.bytes | CLOSED Lean pairing; native contexts pass (below) |
| E.to_le_bytes | canonical8 limbs | LPi_EWriter.source reuses unchanged emitted serializer and exact ordered8 LE word layout under explicit P6 model | CLOSED Lean value pairing; std/iterator ABI retained in D188 |

No unpaired stub is accepted as closure. Writers must constrain every written byte to the four-byte little-endian word layout and preserve all bytes outside their passed slice by Rust borrowing. A stronger whole-buffer frame needs caller-context checking.

FIo_FieldValues import exploration hit missing PAln_RowBounds/Port5Q1_Ten. LPi_missing.json is a SOURCE import inventory, not proof that all listed modules are absent from the actual object closure. No shared object was changed; direct natural coordinate laws avoid this unrelated closure. Failed axioms reports containing sorryAx are excluded.

LPi_ByteWord.source audits the literal emitted M31 byte result before the accepted mbytes caller runs. Rust replacements are retained in LPi_harness.patch and exact per-run patches, not loose Rust files.

L016 was rejected by the unchanged runner before Lean launched because its direct prerequisite LPi_CMProduct had not yet compiled. This was a correct dependency preflight rejection, not a launcher repair. L017 supplies the missing object; L018 then reached elaboration. No admission rejection was bypassed.

## Installed caller stubs and domains

| Rust replacement | Target | Paired theorem / exact domain | Native result |
|---|---|---|---|
| LPi_contracts::mbytes | M31::to_le_bytes | LPi_ByteWord.source, every U32 | K002–004 CM31 contexts pass |
| LPi_contracts::cbytes | CM31::write_le_bytes | LPi_WriterValues.cm_writer, raw limbs, passed slice length8 | K005–010 QM31 contexts pass |
| LPi_contracts::qbytes | QM31::write_le_bytes | LPi_WriterValues.qm_writer, raw limbs, passed slice length16 | K012 private put_k for every prefix0..1720 passes |
| LPi_contracts::ebytes | E::to_le_bytes | LPi_EWriter.source, every emitted8-limb value under explicit P6 iterator model | K013 private put for every prefix0..1704 passes; std/iterator ABI still D188 |
| LPi_contracts::emul | E::mul | LPi_TowerValues.wide_mul, canonE inputs; exact natural mulE specification and canonical result | K014 timed out; no native continuing-iteration pass |

All installed stubs choose nondeterministic result bytes/limbs, assume exactly
the paired value predicate, and check required caller slice lengths or use E's
validated private coordinates. Lower multiplication operations are discharged
by the named Lean coordinate theorems; no native Kani multiplication is run.
Only the outer E multiply stub is installed in the powers caller. Q.raw is
associated directly in Lean by LPi_RawAssociation/RawValues, with no opaque
Rust substitution credited. Thus theorem availability is not confused with
a completed native caller harness for every table row.

The canonical input requirements of the field laws are explicit obligations
of the remaining whole prepared_claim caller join. LPi_CheckedInputs transports
canonical E/Q coordinates into the private Q domain; it does not prove that
every semantic read in that whole caller has yet been associated. No stronger
caller precondition is silently accepted as a leaf pass. The E writer theorem
uses the explicit P6 iterator interpretation; its native std/ABI obligation is
retained, not converted to an extra axiom.
