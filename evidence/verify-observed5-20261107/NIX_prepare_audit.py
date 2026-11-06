from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'verify-observed4-20261107';N=E.parent/'owner-dedupe-20261107';accepted={}
for p in sorted(E.glob('NIX_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text())
 if r['kind']=='lean' and r['exit_status']==0:accepted[r['module']]=r
mods=[];roots=['AspisR1.RPx_Deployed.deployed'];rejected=[]
for p in sorted(E.glob('NIX_*.lean')):
 if p.stem in ['NIX_COMBINED_IMPORT','NIX_Driver','NIX_ProofDriver'] or not re.search(r'^\s*theorem ',p.read_text(),re.M):continue
 r=accepted.get(p.stem);sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if not r or r['source_hashes'].get('NIX_generated/'+p.name)!=sha:
  rejected.append(dict(module=p.stem,source_sha256=sha,reason='No successful current-source receipt; no object/theorem credit'));continue
 mods.append(dict(module=p.stem,attempt=r['attempt'],sha256=sha))
 for line in r['print_axioms']:
  assert 'sorryAx'not in line,line
  m=re.match("'([^']+)'",line)
  if m and m[1]not in roots:roots.append(m[1])
(E/'NIX_MODULES.json').write_text(json.dumps(mods,indent=2)+'\n');(E/'NIX_REJECTED_DRAFTS.json').write_text(json.dumps(rejected,indent=2)+'\n');(E/'NIX_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots[i:i+32] for i in range(0,len(roots),32)]),indent=2)+'\n')
imports=['NIX_BASE_IMPORT',*[r['module'] for r in mods]];body='\n'.join('import '+n for n in imports)+'\n'+'\n'.join('#print axioms '+r for r in roots)+'\n';(E/'NIX_COMBINED_IMPORT.lean').write_text(body)
rows={}
for path in [P/'NIH_EXPECTED_IMPORTS.jsonl',N/'NIM_EXPECTED_IMPORTS.jsonl']:
 for r in map(json.loads,path.read_text().splitlines()):
  if r['module']in rows and rows[r['module']]!=r:
   assert r['module']=='NGC_MemoryLimit' and r['imports']==['Init','all'] and rows[r['module']]['imports']==['Init','Lean.Shell'],'unreviewed import conflict'
   continue # source import all Lean.Shell; NIM regex captured its keyword, not module name
  rows[r['module']]=r
for module in [*[r['module'] for r in mods],'NIX_EmittedTypes','NIX_BASE_IMPORT','NIX_COMBINED_IMPORT']:
 src=(E/(module+'.lean')).read_text();rows[module]=dict(module=module,imports=['Init',*re.findall(r'^import ([\w.]+)',src,re.M)])
(E/'NIX_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[k])+'\n' for k in sorted(rows)))
for name in ['Driver','ProofDriver']:
 src=(P/('NIH_'+name+'.lean')).read_text();new=src.replace('NIH_','NIX_');(E/('NIX_'+name+'.lean')).write_text(new);(E/('NIX_'+name+'.diff')).write_text(''.join(difflib.unified_diff(src.splitlines(True),new.splitlines(True),fromfile='NIH_'+name+'.lean',tofile='NIX_'+name+'.lean')))
for name in ['link.py','batch.py']:(E/('NIX_'+name)).write_text((P/('NIH_'+name)).read_text().replace('NIH_','NIX_'))
D=E/'NIX_native';D.mkdir(exist_ok=True)
for name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 src=P/'NIH_L084/sources/NIH_native'/name;assert src.is_file();(D/name).write_bytes(src.read_bytes())
print(json.dumps(dict(modules=len(mods),roots=len(roots),groups=(len(roots)+31)//32,rejected=rejected)))
