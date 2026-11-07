"""Own audit inputs; unchanged NFX and raw ax2 walker semantics."""
from pathlib import Path
import json,re,hashlib,shutil,difflib
E=Path(__file__).resolve().parent;P=E.parent/'tx1-observed2-20261110';L=E.parent/'ledger24-20261110'
latest={}
for p in sorted(E.glob('NMP_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());m=r.get('module','');s=E/'NMP_generated'/(m+'.lean');q=p.parent/'sources/NMP_generated'/(m+'.lean')
 if r['kind']=='lean' and r['exit_status']==0 and s.is_file() and q.is_file() and s.read_bytes()==q.read_bytes():latest[m]=(r,p)
mods=sorted(m for m in latest if m not in ['NMP_COMBINED_IMPORT','NMP_Driver','NMP_ProofDriver']);roots=[]
for m in mods:
 r,p=latest[m];roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",(p.parent/'stdout.log').read_text())
roots=sorted(set(roots));assert {'NMP_Resource137','NMP_Resource087','NMP_Composition137'}.issubset(mods)
headline='AspisR1.RPx_Deployed.deployed'
text='import NLX_COMBINED_IMPORT\nimport NLZ_COMBINED_IMPORT\nimport NLR_COMBINED_IMPORT\nimport NLJ_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in mods)+'\nset_option pp.proofs false\n'
for n in [headline]+roots:text+='#print axioms '+n+'\n#check @'+n+'\n'
(E/'NMP_generated/NMP_COMBINED_IMPORT.lean').write_text(text);(E/'NMP_COMBINED_IMPORT.lean').write_text(text)
(E/'NMP_MODULES.json').write_text(json.dumps(dict(modules=mods,roots=roots,selected_receipts={m:str(latest[m][1].relative_to(E))for m in mods},row_roots=[]),indent=1))
(E/'NMP_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots+[headline],groups=([roots[i::27] for i in range(27)]+[[headline]]))))
(E/'NMP_AUDIT_MODULES.json').write_text(json.dumps([['NMP_COMBINED_IMPORT'] for _ in range(28)]))
expected={};conflicts=[]
for d,tag in [(P,'NLZ'),(L,'NLX')]:
 for line in (d/(tag+'_EXPECTED_IMPORTS.jsonl')).read_text().splitlines():
  x=json.loads(line)
  if x['module']in expected and expected[x['module']]['imports']!=x['imports']:conflicts.append([expected[x['module']],x])
  expected[x['module']]=x
assert not conflicts,conflicts
for m in mods+['NMP_COMBINED_IMPORT']:
 imports=['Init']+re.findall(r'^import (?:all )?([\w.]+)',(E/'NMP_generated'/(m+'.lean')).read_text(),re.M)
 expected[m]=dict(module=m,imports=list(dict.fromkeys(imports)))
(E/'NMP_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[k])+'\n'for k in sorted(expected)))
diff=''
for name in ['Driver','ProofDriver']:
 a=(P/'NLZ_generated'/('NLZ_'+name+'.lean')).read_text();b=a.replace('NLZ_','NMP_')
 (E/'NMP_generated'/('NMP_'+name+'.lean')).write_text(b)
 diff+=''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='NLZ_'+name+'.lean',tofile='NMP_'+name+'.lean'))
(E/'NMP_DRIVER_DIFF.patch').write_text(diff)
(E/'NMP_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:shutil.copyfile(P/'NLZ_native'/n,E/'NMP_native'/n)
pins={n:hashlib.sha256((E/n).read_bytes()).hexdigest()for n in ['NMP_AUDIT_ROOTS.json','NMP_AUDIT_MODULES.json','NMP_EXPECTED_IMPORTS.jsonl','NMP_native/NFA_WALKER.c','NMP_native/NFA_MemoryLimit.c']}
(E/'NMP_AUDIT_MANIFEST_PINS.json').write_text(json.dumps(pins,indent=1))
print(json.dumps(dict(modules=len(mods),new_roots=len(roots),groups=28,expected_import_conflicts=0)))
