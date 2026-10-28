from pathlib import Path
import json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028';P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';chunks=json.loads((E/'mask-chunks.json').read_text())
name='PV_RDB2D_MasksValue';s='import R1Z.PV_RDB2D_MaskChunk13\nnamespace R1Z.'+name+'\nopen PV_RDB2D_MasksLoop\nset_option autoImplicit false\n'
s+='def initial : Masks := PV_RDB2D_MaskChunk00.before\ndef value : Masks := PV_RDB2D_MaskChunk13.after\n'
parts=[f'PV_RDB2D_MaskChunk{i:02}.rows' for i in range(14)];right=parts[-1]
for x in reversed(parts[:-1]):right=x+' ++ ('+right+')'
s+='theorem rows_split : PV_B3P_Sorted133.expected = '+right+' := by\n  simp only ['+','.join(['PV_B3P_Sorted133.expected']+[f'PV_RDB2D_MaskChunk{i:02}.rows'for i in range(14)]+['List.cons_append','List.nil_append'])+']\n  rfl\n'
s+='theorem concrete : run PV_B3P_Sorted133.expected initial=value := by\n  rw [rows_split]\n  unfold initial value\n'
for i in range(13):s+=f'  rw [append,PV_RDB2D_MaskChunk{i:02}.value]\n'
s+='  exact PV_RDB2D_MaskChunk13.value\n'
s+='theorem length : value.length=64 := rfl\n'
s+='theorem native_rows : run (PV_B3P_Install133.value.val.map (fun x => x.val)) initial=value := by\n  rw [PV_B3P_Closure133.value_nat,concrete]\n'
s+='\n#print axioms rows_split\n#print axioms concrete\n#print axioms length\n#print axioms native_rows\nend R1Z.'+name+'\n';(P/(name+'.lean')).write_text(s)
