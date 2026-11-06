from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'verify-observed5-20261107';U=E.parent/'ledger13-20261107';accepted={}
for p in sorted(E.glob('NJG_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text())
 if r['kind']=='lean' and r['exit_status']==0:accepted[r['module']]=r
mods=[];roots=['AspisR1.RPx_Deployed.deployed'];rejected=[]
for p in sorted(E.glob('NJG_*.lean')):
 if p.stem in ['NJG_BASE_IMPORT','NJG_COMBINED_IMPORT','NJG_Driver','NJG_ProofDriver']:continue
 r=accepted.get(p.stem);h=hashlib.sha256(p.read_bytes()).hexdigest()
 if not r or r['source_hashes'].get('NJG_generated/'+p.name)!=h:
  rejected.append(dict(module=p.stem,source_sha256=h,reason='No successful current-source receipt; never imported or credited'));continue
 mods.append(dict(module=p.stem,attempt=r['attempt'],sha256=h))
 for line in r['print_axioms']:
  assert 'sorryAx' not in line,line
  m=re.match("'([^']+)'",line)
  if m and m[1]not in roots:roots.append(m[1])
(E/'NJG_MODULES.json').write_text(json.dumps(mods,indent=2));(E/'NJG_REJECTED_DRAFTS.json').write_text(json.dumps(rejected,indent=2));(E/'NJG_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots[i:i+32] for i in range(0,len(roots),32)]),indent=2))
(E/'NJG_BASE_IMPORT.lean').write_text('import NGK_COMBINED_IMPORT\nimport NIU_COMBINED_IMPORT\nimport NIX_COMBINED_IMPORT\n#print axioms AspisR1.RPx_Deployed.deployed\n')
(E/'NJG_COMBINED_IMPORT.lean').write_text('\n'.join('import '+n for n in ['NJG_BASE_IMPORT',*[m['module'] for m in mods]])+'\n'+'\n'.join('#print axioms '+n for n in roots)+'\n')
rows={};variants=[]
for path in [U/'NIU_EXPECTED_IMPORTS.jsonl',P/'NIX_EXPECTED_IMPORTS.jsonl']:
 for r in map(json.loads,path.read_text().splitlines()):
  if r['module']in rows and rows[r['module']]!=r:
   variants.append(dict(module=r['module'],selected=rows[r['module']],other=r));continue
  rows[r['module']]=r
for n in [*[m['module'] for m in mods],'NJG_BASE_IMPORT','NJG_COMBINED_IMPORT']:
 text=(E/(n+'.lean')).read_text();rows[n]=dict(module=n,imports=['Init',*re.findall(r'^import ([\w.]+)',text,re.M)])
(E/'NJG_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[n])+'\n' for n in sorted(rows)));(E/'NJG_IMPORT_VARIANTS.json').write_text(json.dumps(variants,indent=2))
for name in ['Driver','ProofDriver']:
 src=(P/('NIX_'+name+'.lean')).read_text();new=src.replace('NIX_','NJG_');(E/('NJG_'+name+'.lean')).write_text(new);(E/('NJG_'+name+'.diff')).write_text(''.join(difflib.unified_diff(src.splitlines(True),new.splitlines(True),fromfile='NIX_'+name+'.lean',tofile='NJG_'+name+'.lean')))
for name in ['link.py','batch.py','audit_all.py']:(E/('NJG_'+name)).write_text((P/('NIX_'+name)).read_text().replace('NIX_','NJG_'))
D=E/'NJG_native';D.mkdir(exist_ok=True)
for name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 src=P/'NIX_native'/name
 if not src.is_file():src=P/'NIX_L096/sources/NIX_native'/name
 assert src.is_file(),src
 (D/name).write_bytes(src.read_bytes())
print(json.dumps(dict(modules=len(mods),roots=len(roots),groups=(len(roots)+31)//32,rejected=len(rejected),import_variants=len(variants))))
