from pathlib import Path
import subprocess,re,json,hashlib
P=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');E=Path('evidence/pv-op223-20261027');D='/home/dombarker/project-offloads/codex-pv-op223-20261027';H='dombarker@100.108.41.90'
raw={k:subprocess.check_output(['ssh',H,'cat '+D+'/applied-generated/'+k],text=True) for k in ['Funs.lean','Types.lean','translation.json']}
for k,v in raw.items():(E/('raw-'+k.replace('.json','.json.txt'))).write_text(v)
meta=json.loads(raw['translation.json']);assert not any(f['is_opaque'] for f in meta['functions']);assert 'FunsExternal' not in raw['Funs.lean']
(P/'PV_Op223_Carrier.lean').write_text('''import R1Z.PV_Ext_ClosedCarrier
namespace PV_Op223_Applied
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
end PV_Op223_Applied
''')
header,rest=raw['Funs.lean'].split('namespace PV_Op223_Applied\n',1);rest=rest.rsplit('end PV_Op223_Applied',1)[0];blocks=[b for b in re.split(r'(?=/-- \[)',rest) if b.strip()];prev='PV_Op223_Carrier';rows=[]
for i,b in enumerate(blocks):
 name=re.search(r'\bdef\s+([\w.]+)',b)[1];short=name.replace('aspis_core.field.','').replace('prover_shared.compress_tagged_tuple','compress').replace('.','_');mod=f'PV_Op223_Extract_{i:02}_{short}'
 h=header.replace('import PVOp223Applied.Types','import R1Z.'+prev)
 b=re.sub(r'(\b(?:Std\.)?U(?:8|16|32|64|128|size)\.wrapping_shr [A-Za-z_][\w.]* )(\d+)#i32\b',lambda m:m[1]+m[2]+'#u32',b).replace('core.num.Usize.wrapping_add','Std.Usize.wrapping_add')
 s=h+'namespace PV_Op223_Applied\n'+b+'\n#print axioms '+name+'\nend PV_Op223_Applied\n'
 (P/(mod+'.lean')).write_text(s);rows.append(dict(module='R1Z/'+mod,declaration='PV_Op223_Applied.'+name,raw_sha256=hashlib.sha256(blocks[i].encode()).hexdigest()));prev=mod
(E/'extraction-split.json').write_text(json.dumps(dict(raw_hashes={k:hashlib.sha256(v.encode()).hexdigest() for k,v in raw.items()},modules=rows,adaptations=['import relocation','structurally identical carriers','unsigned shift literal for pinned backend','Usize wrapping_add backend name'],opaque_functions=0),indent=2)+'\n')
# Compare arithmetic declarations symbolically with earlier standalone extraction;
# each equality unfolds its declaration only, rewriting already named predecessors.
prev='PV_Op223_FieldBridge_QM31_mul_m31';laws=[]
for i,row in enumerate(rows[:23]):
 name=row['declaration'].removeprefix('PV_Op223_Applied.');tag=name.removeprefix('aspis_core.field.').replace('.','_');mod='PV_Op223_Agreement_'+tag
 lhs=row['declaration'];rhs='PV_Ext_IndexClosed.'+name
 proof='by\n  unfold '+lhs+' '+rhs+'\n  simp only ['+', '.join(laws)+']' if laws else 'by\n  unfold '+lhs+' '+rhs+'\n  rfl'
 s='import '+row['module'].replace('/','.')+'\nimport R1Z.'+prev+'\nopen Aeneas Aeneas.Std Result\nnamespace R1Z.PV_Op223_Agreement\ntheorem '+tag+' : '+lhs+' = '+rhs+' := '+proof+'\n#print axioms '+tag+'\nend R1Z.PV_Op223_Agreement\n'
 (P/(mod+'.lean')).write_text(s);laws.append('R1Z.PV_Op223_Agreement.'+tag);prev=mod
