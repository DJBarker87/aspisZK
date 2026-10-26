"""Forward native strict records over the retained fixture; symbolic value expansion."""
from pathlib import Path
import argparse,hashlib,json
R=Path(__file__).resolve().parents[2]
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
manifest=json.loads((R/'evidence/joint-fixture3-20261026/JFz_ROWS_MANIFEST.json').read_text())
fixture=R/'docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/transfer-13/r1-s2-proof.bin'
b=fixture.read_bytes();assert len(b)==57607
out=[]
for row in manifest:
 i=row['row'];o=row['offset'];size=row['logical_bytes'];stored=row['stored_bytes'];tag=row['tag'];mod=f'JFw_NativeRow{i:02}'
 assert b[o:o+5]==bytes([tag])+size.to_bytes(4,'little')
 head=list(b[o:o+5]);headstr=','.join(f'{x}#u8' for x in head);params=' '.join(f'{x}#u8' for x in head)
 lines=['import JFw_Frames','import JFw_Record',f'import JFz_Row{i:02}','import ExtractedRecordFraming','set_option autoImplicit false','noncomputable section',f'namespace AspisR1.{mod}','open Aeneas Aeneas.Std Result','open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical JFw_Frames']
 if i>=14:
  n=size//32
  lines += [f'def payload : Slice U8 := expandedPayload {n} {o+5} (by decide) (by decide)',f'theorem payload_length : payload.length = {size} := expanded_length {n} {o+5} (by decide) (by decide)',f'theorem fields : AspisR1RecordParser.r1_wire.validate_record_fields {i}#u8 payload = ok (.Ok ()) := by',f'  apply JFw_BlockValidation.success {n} (window {o+5} {stored}).val payload {i}#u8',f'  · exact window_length {o+5} {stored} (by decide)','  · scalar_tac',f'  · rw [window_bytes];exact JFz_Scan{47+i-14:02}.canonical_selected',f'  · exact JFw_Blocks.bytes {n} _']
 else:
  lines += [f'def payload : Slice U8 := window {o+5} {size}',f'theorem payload_length : payload.length = {size} := window_length {o+5} {size} (by decide)']
 lines += [f'def record : Slice U8 := frame {params} payload (by rw [payload_length];decide)',f'theorem source_shape : AspisR1RecordParser.r1_wire.row_shape {i}#u8 = ok (some ({tag}#u8,{size}#usize)) := by', '  rw [ExtractedRecordFraming.parser_row_shape_table]','  rfl',f'theorem accepted : AspisR1PrefixAggregateParser.r1_wire.parse_record {i}#u8 record = ok (.Ok payload) := by', '  apply JFw_CurrentValidation.record', f'  apply JFw_Record.success {i}#u8 {params} {size}#usize record payload source_shape (by decide) payload_length rfl', '  · apply UScalar.eq_of_val_eq;scalar_tac']
 if i>=14:lines+=['  · intro _;exact fields']
 else:lines+=['  · intro h;scalar_tac']
 lines += [f'theorem bytes : bytesOf record.val = PSem_Rows.expandedRow {i} (slice JFz_RowGeometry.wire {o} {7031-o}) := by', f'  have head : (slice JFz_RowGeometry.wire {o} {7031-o}).take 5 = bytesOf [{headstr}] := by',f'    rw [JFz_RowGeometry.slice_take _ {o} 5 {7031-o} (by decide)]',f'    simp only [slice,JFz_RowGeometry.wire,bytesOf,←List.map_drop,←List.map_take,JFz_Row{i:02}.header]',f'  simp only [PSem_Rows.expandedRow,JFz_Row{i:02}.shape,Prod.snd,if_'+('pos' if i>=14 else 'neg')+f' (by decide : '+('' if i>=14 else '¬ ')+f'14 ≤ {i}),head]',f'  rw [JFz_RowGeometry.slice_slice _ {o} {7031-o} 5 {stored} (by decide)]']
 if i>=14:lines += [f'  have pbytes := expanded_bytes {size//32} {o+5} (by decide) (by decide)',f'  change bytesOf ([{headstr}] ++ payload.val) = _', '  rw [MultiproofConeExpandModel.bytes_append]','  exact congrArg (fun tail => bytesOf ['+headstr+'] ++ tail) pbytes']
 else:lines += [f'  change bytesOf ([{headstr}] ++ payload.val) = _','  rw [MultiproofConeExpandModel.bytes_append,payload,window_bytes]']
 lines += ['#print axioms payload_length']+(['#print axioms fields'] if i>=14 else [])+['#print axioms source_shape','#print axioms accepted','#print axioms bytes',f'end AspisR1.{mod}','end']
 text='\n'.join(lines)+'\n';target=R/'lean'/f'{mod}.lean'
 if args.check:assert target.read_text()==text,target
 else:target.write_text(text)
 out.append(dict(row=i,module=mod,source_sha256=hashlib.sha256(text.encode()).hexdigest()))
meta=dict(fixture=str(fixture.relative_to(R)),fixture_sha256=hashlib.sha256(b).hexdigest(),rows=out)
target=R/'evidence/joint-fixture4-20261026/JFw_RECORDS_MANIFEST.json'
if args.check:assert json.loads(target.read_text())==meta
else:target.write_text(json.dumps(meta,indent=2)+'\n')
