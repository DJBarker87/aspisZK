from pathlib import Path
import json,re
E=Path('evidence/pv-batch2-20261027');L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');rows=json.loads((E/'constructor-split.json').read_text())['modules'][:20]
prev='PV_B2_WeightsNativeTypes';laws=[];mods=[]
for i,row in enumerate(rows):
 name=row['name'];tag=name.removeprefix('aspis_core.field.').replace('.','_');mod='PV_B2_Total_'+tag
 source=(L/(row['module'].split('/')[-1]+'.lean')).read_text();body=source.split('namespace PV_B2_WeightsNative\n',1)[1].split('\n#print axioms')[0]
 body=re.sub(r'/--.*?-/', '',body,flags=re.S);body=re.sub(r'@\[.*?\]\s*','',body,flags=re.S).strip()
 m=re.search(r'def ([\w.]+)\s*((?:\([^)]*\)\s*)*):\s*Result ([\w.]+)\s*:= do\n',body)
 if m:
  args=m[2];names=[x.strip().split(':')[0].strip() for x in re.findall(r'\(([^)]*)\)',args)]
  pure=body[:m.end()].replace('Result '+m[3],m[3]).replace(':= do',':=')+body[m.end():]
  pure=re.sub(r'let (\w+) ← lift \(([^\n]*)\)',r'let \1 := (\2)',pure)
  pure=pure.replace(' ← ', ' := ');pure=re.sub(r'\bok ', '',pure)
  statement=args+': PV_B2_WeightsNative.'+name+' '+ ' '.join(names)+' = ok (PV_B2_FieldValue.'+name+' '+' '.join(names)+')'
 else:
  pure=body;statement=': PV_B2_WeightsNative.'+name+' = PV_B2_FieldValue.'+name
 carrier='namespace PV_B2_FieldValue\n'+''.join('abbrev aspis_core.field.'+n+' := ProverRwFull.aspis_core.field.'+n+'\n' for n in ['M31','CM31','QM31']) if i==0 else 'namespace PV_B2_FieldValue\n'
 text='import '+row['module'].replace('/','.')+'\nimport R1Z.'+prev+'\nopen Aeneas Aeneas.Std Result\n'+carrier+pure+'\nend PV_B2_FieldValue\nnamespace PV_B2_FieldTotal\n/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/\ntheorem '+tag+' '+statement+' := by\n  unfold PV_B2_WeightsNative.'+name+' PV_B2_FieldValue.'+name+'\n  '+('rfl' if not laws else 'simp only ['+', '.join(laws)+',lift,bind_tc_ok]')+'\n#print axioms '+tag+'\nend PV_B2_FieldTotal\n'
 (L/(mod+'.lean')).write_text(text);mods.append('R1Z/'+mod);prev=mod;laws.append('PV_B2_FieldTotal.'+tag)
(E/'pure-field-queue.json').write_text(json.dumps(mods,indent=2)+'\n')
