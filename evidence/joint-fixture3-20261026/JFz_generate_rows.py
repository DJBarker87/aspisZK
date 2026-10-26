"""Bounded per-row retained frame headers; no acceptance claim is generated."""
from pathlib import Path
import json,re,argparse,hashlib
R=Path(__file__).resolve().parents[2];p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
b=(R/'docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/transfer-13/r1-s2-proof.bin').read_bytes()
off=48;rows=[]
for row in range(27):
 tag,size=(1,32) if row==2 else (3,32) if row==14 else (2,896) if 15<=row<=24 else (4,3712) if row==25 else (5,928) if row==26 else (0,0)
 n=size//2 if row>=14 else size;assert b[off:off+5]==bytes([tag])+size.to_bytes(4,'little')
 mod=f'JFz_Row{row:02d}';lines=['import JFz_RowGeometry','import JFx_NativeBytes','set_option autoImplicit false','set_option linter.unusedSimpArgs false','noncomputable section',f'namespace AspisR1.{mod}','open Aeneas Aeneas.Std','open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical JFz_RowGeometry',f'theorem header : (JFx_NativeBytes.proof.val.drop {off}).take 5 = ['+','.join(f'{v}#u8' for v in b[off:off+5])+'] := by','  change (JFx_NativeBytes.proofBytes.drop _).take _ = _']
 base=['JFx_NativeBytes.proofBytes','List.drop_append','List.take_append','List.length_append']+[f'JFx_DataProof{z:02d}.length' for z in range(15)]+['Nat.reduceAdd','Nat.reduceSub','Nat.reduceLeDiff','List.length_drop','List.drop_eq_nil_of_le','List.take_of_length_le','List.drop_zero','List.take_zero','List.nil_append','List.append_nil']
 lines += ['  simp only ['+','.join(base)+']']
 pref=f'JFx_DataProof{off//4096:02d}'
 simp=[pref+'.bytes']+[pref+f'.c{c:02d}_length' for c in range(128)]+['List.drop_append','List.take_append','List.length_append','Nat.reduceAdd','Nat.reduceSub','Nat.reduceLeDiff','List.length_drop','List.drop_eq_nil_of_le','List.take_of_length_le','List.drop_zero','List.take_zero','List.nil_append','List.append_nil']
 lines+=['  simp only ['+','.join(simp)+']','  rfl','#print axioms header']
 if row>=14:lines.insert(0,f'import JFz_Scan{47+row-14:02d}')
 compact=f'if_pos (by decide : 14 ≤ {row})' if row>=14 else f'if_neg (by decide : ¬ 14 ≤ {row})'
 lines += [f'theorem shape : rowShape {row} = ({tag},{size}) := by norm_num [rowShape]',
   f'theorem step (rs : List Bytes)',
   f'    (tail : semanticRows {26-row} {row+1} (slice wire {off+5+n} {7031-off-5-n}) = some rs) :',
   f'    semanticRows {27-row} {row} (slice wire {off} {7031-off}) =',
   f'      some (PSem_Rows.expandedRow {row} (slice wire {off} {7031-off}) :: rs) := by',
   f'  refine JFz_RowGeometry.forward {26-row} {row} _ rs ?_ ?_ ?_ ?_',
   f'  · norm_num only [shape,Prod.snd,{compact}]',
   '    rw [slice,List.length_take,List.length_drop,wire_length]',
   '    decide',
   '  · rw [shape]',
   f'    rw [slice_take _ {off} 5 {7031-off} (by decide)]',
   '    simp only [slice,wire,bytesOf, ← List.map_drop, ← List.map_take,header]',
   '    rfl',
   '  · intro compact']
 if row>=14:
  lines += [f'    rw [shape]',f'    change canonical (slice (slice wire {off} {7031-off}) 5 {n})',f'    rw [slice_slice _ {off} {7031-off} 5 {n} (by decide)]',f'    exact JFz_Scan{47+row-14:02d}.canonical_selected']
 else:lines+=['    omega']
 lines += [f'  · norm_num only [shape,Prod.snd,{compact}]',f'    rw [slice_drop]',f'    exact tail','#print axioms shape','#print axioms step',f'end AspisR1.{mod}','end']
 text='\n'.join(lines)+'\n';target=R/'lean'/f'{mod}.lean'
 if args.check:assert target.read_text()==text
 else:target.write_text(text)
 rows.append({'row':row,'module':mod,'offset':off,'tag':tag,'logical_bytes':size,'stored_bytes':n,'source_sha256':hashlib.sha256(text.encode()).hexdigest()});off+=5+n
assert off==7031
out=R/'evidence/joint-fixture3-20261026/JFz_ROWS_MANIFEST.json'
if args.check:assert json.loads(out.read_text())==rows
else:out.write_text(json.dumps(rows,indent=2)+'\n')
