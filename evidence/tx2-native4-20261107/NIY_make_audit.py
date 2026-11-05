"""Adapt only root/module lists of retained audit drivers; scan algorithm unchanged."""
from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'tx2-native3-20261107'
selected={}
for p in sorted(E.glob('NIY_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text())
 if r['kind']!='lean' or r['exit_status']!=0:continue
 m=r['module'];src=E/(m+'.lean')
 if not src.exists() or m in ['NIY_Driver','NIY_ProofDriver','NIY_COMBINED_IMPORT']:continue
 n='NIY_generated/'+m+'.lean'
 if r['source_hashes'].get(n)!=hashlib.sha256(src.read_bytes()).hexdigest():continue
 selected[m]=dict(module=m,receipt=str(p.relative_to(E)),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest())
mods=list(selected);roots=[]
for m in mods:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 roots += [ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
 if m=='NIY_NativeCuts':roots += ['NIY_NativeCuts.'+n for n in ['firstByte','firstCursor','eReply','kReply','eValue','kValue','descriptor','eCursor','kCursor']]
for mod,names in {'NIY_NativeFinalCuts':['windowPre','windowCut','reserveCut','weightPre','weightCut'],'NIY_ScanCuts':['prefixCut','m31Cut','openingCut']}.items():
 if mod in mods:roots += [mod+'.'+n for n in names]
roots+=['AspisR1.RPx_Deployed.deployed'];groups=[roots[i:i+20] for i in range(0,len(roots),20)]
(E/'NIY_MODULES.json').write_text(json.dumps(dict(selected=list(selected.values())),indent=2)+'\n')
(E/'NIY_COMBINED_IMPORT.lean').write_text('import NGK_COMBINED_IMPORT\nimport NID_COMBINED_IMPORT\nimport NIL_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in roots))
(E/'NIY_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=groups),indent=2)+'\n')
s=(P/'NIL_ProofDriver.lean').read_text();a=s.index('    else if mode == "proof0"');b=s.index('    else (#[], #[])',a)
branches=''
for i,g in enumerate(groups):branches+='    else if mode == "proof'+str(i)+'" then\n      (#[`NIY_COMBINED_IMPORT], #['+', '.join('`'+n for n in g)+'])\n'
s=s[:a]+branches+s[b:];(E/'NIY_ProofDriver.lean').write_text(s)
(E/'NIY_PROOF_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NIL_ProofDriver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NIL_ProofDriver.lean',tofile='NIY_ProofDriver.lean')))
s=(P/'NIL_Driver.lean').read_text().replace('NIL_','NIY_');(E/'NIY_Driver.lean').write_text(s)
(E/'NIY_SCAN_DRIVER.diff').write_text(''.join(difflib.unified_diff((P/'NIL_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NIL_Driver.lean',tofile='NIY_Driver.lean')))
batch=(P/'NIL_batch.py').read_text().replace('NIL_','NIY_')
batch=batch.replace("if mode.startswith('inventory-'):","if mode=='all':jobs=[('proof'+str(i),['NIY_native/NIY_ProofDriver','proof'+str(i)]) for i in range(len(json.loads((B/'NIY_AUDIT_ROOTS.json').read_text())['groups']))]\nelif mode.startswith('inventory-'):")
(E/'NIY_batch.py').write_text(batch)
rows=[json.loads(l) for l in (P/'NIL_LOADED_scan.jsonl').read_text().splitlines()];expect={r['module']:r['imports'] for r in rows}
for m in mods+['NIY_COMBINED_IMPORT']:
 imports=['Init']
 for name in re.findall(r'^import (.+)$',(E/(m+'.lean')).read_text(),re.M):
  for n in name.split():
   if n not in imports:imports.append(n)
 expect[m]=imports
(E/'NIY_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=v))+'\n' for n,v in sorted(expect.items())))
(E/'NIY_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:(E/'NIY_native'/n).write_bytes((P/'NIL_native'/n).read_bytes())
print(json.dumps(dict(selected_modules=len(mods),audited_roots=len(roots),groups=len(groups),scope='gate preparation only; no credit until every gate passes')))
