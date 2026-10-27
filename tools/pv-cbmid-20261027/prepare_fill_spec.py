"""Compose opaque literal blocks through generic length/capacity/append lemmas."""
from pathlib import Path
import json,hashlib,sys
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cbmid-20261027';d=json.loads((out/'REFERENCE-CANDIDATE.json').read_text());sizes=d['chunk_sizes']
name='PV_CBM_CellsSpec';p=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'/f'{name}.lean'
s='import R1Z.PV_CBM_CellsMaterializer\nimport R1Z.PV_CBM_ListComposition\nnamespace R1Z.'+name+'\nopen Aeneas Aeneas.Std Result\nset_option autoImplicit false\n'
s+='-- Keep literal blocks abstract during composition; their facts are checked separately.\nattribute [local irreducible] '+' '.join(f'PV_CBM_CellChunk{i:02}.literals' for i in range(len(sizes)))+'\n'
s+='abbrev Cell := ProverRwFull.aspis_statement.trace_v4.TraceCell\n'
s+='def literals : List Cell :=\n  '+' ++\n  '.join(f'PV_CBM_CellChunk{i:02}.literals' for i in range(len(sizes)))+'\n'
s+='theorem length : literals.length = 3803 := by\n  simp only [literals,List.length_append,'+','.join(f'PV_CBM_CellChunk{i:02}.length' for i in range(len(sizes)))+']\n'
s+='theorem all_free : ∀ cell ∈ literals, PV_CBM_InventoryShape.free cell.row.val cell.column.val := by\n  unfold literals\n'
proof='PV_CBM_CellChunk00.literals_free'
for i in range(1,len(sizes)):proof=f'PV_CBM_ListComposition.append_free ({proof}) PV_CBM_CellChunk{i:02}.literals_free'
s+='  exact '+proof+'\n'
s+='theorem fill (out : alloc.vec.Vec Cell) (hc : out.val.length+3803≤4096) :\n  ∃ result, PV_CBM_CellsRaw.reference.fill_cells out = ok (.Ok (), result) ∧ result.val = out.val ++ literals := by\n'
s+='  have hl0 : out.val.length = out.val.length + 0 := (Nat.add_zero _).symm\n'
total=0
for i,size in enumerate(sizes):
 before='out' if i==0 else f'out{i}';after=f'out{i+1}';total+=size
 s+=f'  obtain ⟨{after},h{i+1},hv{i+1}⟩ := PV_CBM_CellChunk{i:02}.run {before} (PV_CBM_ListComposition.capacity_step hc hl{i} (by decide))\n'
 s+=f'  have hl{i+1} : {after}.val.length = out.val.length+{total} :=\n    PV_CBM_ListComposition.length_step hv{i+1} PV_CBM_CellChunk{i:02}.length hl{i}\n'
s+=f'  refine ⟨out{len(sizes)},?_,?_⟩\n  · unfold PV_CBM_CellsRaw.reference.fill_cells\n'
for i in range(len(sizes)):s+=f'    rw [h{i+1}]\n    simp only [bind_tc_ok]\n'
s+='  · rw ['+','.join(f'hv{i}' for i in range(len(sizes),0,-1))+']\n    simp only [literals,List.append_assoc]\n'
s+='theorem callback : ∃ result : alloc.vec.Vec Cell,\n    PV_CBM_CellsMaterializer.callback = ok (.Ok result) ∧\n    result.val.length = 3803 ∧\n    (∀ cell ∈ result.val, PV_CBM_InventoryShape.free cell.row.val cell.column.val) := by\n'
s+='  obtain ⟨result,hr,hv⟩ := fill (alloc.vec.Vec.new Cell) (by change 0+3803≤4096; decide)\n  have he : result.val = literals := by simpa only [alloc.vec.Vec.new,List.nil_append] using hv\n  refine ⟨result,?_,?_,?_⟩\n  · unfold PV_CBM_CellsMaterializer.callback\n    rw [hr]\n    exact PV_CBM_CellsMaterializer.snapshot_ok result\n  · rw [he,length]\n  · rw [he]\n    exact all_free\n'
s+='#print axioms length\n#print axioms all_free\n#print axioms fill\n#print axioms callback\nend R1Z.'+name+'\n'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('CHECK' if '--check' in sys.argv else 'GENERATED',name,hashlib.sha256(s.encode()).hexdigest())
