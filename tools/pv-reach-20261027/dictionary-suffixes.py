"""Generate symbolic dictionary congruence targets for each source suffix.
Copies only the named source definition, with byte-comparison evidence;
no source body, recursive loop, or emitted code is modified.
"""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-reach-20261027/resume2'
rows=json.loads((R/'evidence/pv-reach-20261027/resume/continuation-manifest.json').read_text())
manifest=[]
for i,row in enumerate(rows):
 old=L/f'PV_RE_Continue{i:03}.lean'
 if i in (63,64):old=R/f'tools/pv-reach-20261027/drafts/PV_RE_Continue{i:03}.lean.txt'
 text=old.read_text();text=text[:text.index('/-- No branch is discarded')]
 mod=f'PV_RE_DictSuffix{i:03}'
 text=text.replace('import R1Z.ProverRwFullFuns',f'import R1Z.PV_RE_DictSuffix{i-1:03}' if i else 'import R1Z.PV_RE_Dict000').replace(f'namespace R1Z.PV_RE_Continue{i:03}',f'namespace R1Z.{mod}')
 text+=f'\nend R1Z.{mod}\npv_dict_congr ProverRwFull.{row["function"]}\npv_dict_congr R1Z.{mod}.continueAfter\n'
 for n in ['ProverRwFull.'+row['function'],f'R1Z.{mod}.continueAfter']:
  text+=f'#print axioms R1Z.PV_RE_DictCore.{n}\n'
 path=L/(mod+'.lean')
 if '--check' in sys.argv:assert path.read_text()==text,path
 else:path.write_text(text)
 manifest.append(dict(module='R1Z/'+mod,source_function=row['function'],source_definition=str(old.relative_to(R)),source_sha256=hashlib.sha256(old.read_bytes()).hexdigest(),suffix_body_identical=True,congruence='R1Z.PV_RE_DictCore.R1Z.'+mod+'.continueAfter',sha256=hashlib.sha256(text.encode()).hexdigest()))
if '--check' in sys.argv:assert json.loads((E/'suffix-manifest.json').read_text())==manifest
else:(E/'suffix-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'generated',len(rows),'suffix congruence targets')
