from pathlib import Path
import subprocess,re,json,hashlib
P=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');E=Path('evidence/pv-extract-20261027');B='/home/dombarker/project-offloads/codex-pv-extract-20261027/index-closed-generated/'
raw={k:subprocess.check_output(['ssh','dombarker@100.108.41.90','cat '+B+k],text=True) for k in ['Funs.lean','Types.lean','translation.json']}
assert 'FunsExternal' not in raw['Funs.lean'];meta=json.loads(raw['translation.json']);assert not any(f['is_opaque'] for f in meta['functions'])
(P/'PV_Ext_ClosedCarrier.lean').write_text('''import R1Z.ProverRwP7CurrentFieldSource
namespace PV_Ext_IndexClosed
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
end PV_Ext_IndexClosed
''')
s=raw['Funs.lean'];header,rest=s.split('namespace PV_Ext_IndexClosed\n',1);rest=rest.rsplit('end PV_Ext_IndexClosed',1)[0];blocks=re.split(r'(?=/-- \[)',rest);blocks=[b for b in blocks if b.strip()];rows=[];prev='PV_Ext_ClosedCarrier'
for i,b in enumerate(blocks):
 m=re.search(r'\bdef\s+([\w.]+)',b);assert m,b[:100];name=m[1];short=name.replace('aspis_core.field.','').replace('compress_tagged_tuple','compress').replace('.','_');mod=f'PV_Ext_Closed_{i:02}_{short}'
 h=header.replace('import PVExtIndexClosed.Types','import R1Z.'+prev)
 changes=[]
 def shift(m):
  new=m[1]+m[2]+'#u32';changes.append([m[0],new]);return new
 b=re.sub(r'(\b(?:Std\.)?U(?:8|16|32|64|128|size)\.wrapping_shr [A-Za-z_][\w.]* )(\d+)#i32\b',shift,b)
 b=b.replace('core.num.Usize.wrapping_add','Std.Usize.wrapping_add')
 text=h+'namespace PV_Ext_IndexClosed\n'+b+'\n#print axioms '+name+'\nend PV_Ext_IndexClosed\n';(P/(mod+'.lean')).write_text(text)
 rows.append(dict(module='R1Z/'+mod,declaration='PV_Ext_IndexClosed.'+name,raw_block_sha256=hashlib.sha256(blocks[i].encode()).hexdigest(),shift_adaptations=changes));prev=mod
(E/'closed-split.json').write_text(json.dumps(dict(raw_hashes={k:hashlib.sha256(v.encode()).hexdigest() for k,v in raw.items()},modules=rows,carrier='Structurally identical M31/CM31/QM31 relocated to existing ProverRwFull types; no opaque function parameters. Each emitted declaration independently compiled in dependency order; only import/namespace/type-carrier/unsigned-shift-literal/backend wrapping_add normalization.'),indent=2)+'\n');print(len(rows),prev)
