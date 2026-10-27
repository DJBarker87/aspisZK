from pathlib import Path
import re,json,hashlib
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');E=Path('evidence/pv-batch2-20261027');D=E/'extraction-weights/generated-252'
f=(D/'Funs.lean').read_text();t=(D/'Types.lean').read_text()
namespace='PV_B2_WeightsNative'
weights=re.search(r'structure host_weights.Weights where\n.*?(?=\n/--)',t,re.S)[0]
carrier='import R1Z.ProverRwFullTypes\nnamespace '+namespace+'\n'
for n in ['field.M31','field.CM31','field.QM31','circle.SecureCirclePoint']:
 carrier+='abbrev aspis_core.'+n+' := ProverRwFull.aspis_core.'+n+'\n'
for n in ['transport.Variant','verifier.Error']:
 carrier+='abbrev '+n+' := ProverRwFull.'+n+'\n'
carrier+=weights+'\nend '+namespace+'\n'
(L/'PV_B2_WeightsNativeTypes.lean').write_text(carrier)
header,rest=f.split('namespace PV_B2_252\n',1);rest=rest.rsplit('end PV_B2_252',1)[0]
blocks=[b for b in re.split(r'(?=/-- \[)',rest) if b.strip()];prev='PV_B2_WeightsNativeTypes';rows=[]
for i,b in enumerate(blocks):
 name=re.search(r'\bdef\s+([\w.]+)',b)[1];tag=name.removeprefix('aspis_core.field.').replace('.','_');mod=f'PV_B2_W_{i:02}_{tag}'
 h=header.replace('import PVB2252.Types','import R1Z.'+prev)
 b=b.replace('31#i32','31#u32');text=h+'namespace '+namespace+'\n'+b+'\n#print axioms '+name+'\nend '+namespace+'\n'
 (L/(mod+'.lean')).write_text(text);rows.append(dict(module='R1Z/'+mod,name=name,raw_sha256=hashlib.sha256(blocks[i].encode()).hexdigest()));prev=mod
(E/'constructor-split.json').write_text(json.dumps(dict(modules=rows,namespace=namespace,adaptations=['private import paths','structural native carrier aliases','two unsigned shift literals31#u32; same count'],opaque_functions=0),indent=2)+'\n')
prev='ProverRwP7CurrentFieldSource';laws=[];arows=[]
for i,row in enumerate(rows[:20]):
 name=row['name'];tag=name.removeprefix('aspis_core.field.').replace('.','_');mod='PV_B2_Field_'+tag
 lhs=namespace+'.'+name;rhs='R1Z.ProverRwP7CurrentFieldSource.'+name
 if name.endswith('QM31.sub'):
  rhs='(fun (a b : ProverRwFull.aspis_core.field.QM31) => do\n  let c0 ← R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub a.c0 b.c0\n  let c1 ← R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub a.c1 b.c1\n  Aeneas.Std.Result.ok ({c0,c1} : ProverRwFull.aspis_core.field.QM31))'
 proof='by\n  unfold '+lhs+(' '+rhs if name!='aspis_core.field.QM31.sub' else '')+'\n  '+('rfl' if not laws else 'simp only ['+', '.join(laws)+']')
 text='import '+row['module'].replace('/','.')+'\nimport R1Z.'+prev+'\nopen Aeneas Aeneas.Std Result\nnamespace PV_B2_Field\n/-- Exact complete-Result arithmetic comparison on arbitrary raw limbs. -/\ntheorem '+tag+' : '+lhs+' = '+rhs+' := '+proof+'\n#print axioms '+tag+'\nend PV_B2_Field\n'
 (L/(mod+'.lean')).write_text(text);laws.append('PV_B2_Field.'+tag);prev=mod;arows.append('R1Z/'+mod)
(E/'constructor-field-queue.json').write_text(json.dumps(dict(source=[r['module'] for r in rows],agreement=arows),indent=2)+'\n')
