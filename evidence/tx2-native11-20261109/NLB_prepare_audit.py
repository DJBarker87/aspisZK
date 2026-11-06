from pathlib import Path
import json,re,hashlib,subprocess,difflib,lzma
E=Path(__file__).resolve().parent;P=Path('evidence/tx2-native10-20261108')
roots=[]
for p in sorted(E.glob('NLB_*.lean')):
 if p.stem.endswith('Driver') or p.stem=='NLB_COMBINED_IMPORT':continue
 txt=p.read_text();ns=re.findall(r'^namespace (\S+)',txt,re.M)
 if not ns:continue
 roots.extend(ns[0]+'.'+n for n in re.findall(r'^#print axioms (\w+)$',txt,re.M))
roots=list(dict.fromkeys(roots))+['AspisR1.RPx_Deployed.deployed'];groups=[roots[i:i+12] for i in range(0,len(roots),12)]
(E/'NLB_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=groups),indent=2))
for name in ['NLB_Driver','NLB_ProofDriver']:
 old=(P/(name.replace('NLB','NKO')+'.lean')).read_text();s=old.replace('NKO','NLB')
 if name.endswith('ProofDriver'):
  a=s.index('    else if mode == "proof0"');b=s.index('    else (#[], #[])',a)
  part=''.join('    else if mode == "proof'+str(i)+'" then\n      (#[`NLB_COMBINED_IMPORT], #['+', '.join('`'+r for r in group)+'])\n' for i,group in enumerate(groups))
  s=s[:a]+part+s[b:]
 (E/(name+'.lean')).write_text(s)
 (E/(name+'_DIFF.patch')).write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile=name.replace('NLB','NKO')+'.lean',tofile=name+'.lean')))
(E/'NLB_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:(E/'NLB_native'/n).write_bytes((P/'NKO_native'/n).read_bytes())
(E/'NLB_batch.py').write_text((P/'NKO_batch.py').read_text().replace('NKO','NLB'))
rows={};conflicts=[]
for file in ['evidence/ledger20-20261109/NKW_EXPECTED_IMPORTS.jsonl','evidence/tx2-native10-20261108/NKO_BASE_EXPECTED_IMPORTS.jsonl.xz']:
 p=Path(file);txt=lzma.decompress(p.read_bytes()).decode() if p.suffix=='.xz' else p.read_text()
 for line in txt.splitlines():
  r=json.loads(line);old=rows.get(r['module'])
  if old and old['imports']!=r['imports']:conflicts.append(dict(module=r['module'],old=old,new=r))
  rows[r['module']]=r
for p in E.glob('NLB_*.lean'):rows[p.stem]=dict(module=p.stem,imports=re.findall(r'^import (\S+)',p.read_text(),re.M))
# NKO's own modules are not in its inherited baseline.
for p in P.glob('NKO_*.lean'):
 if p.stem.endswith('Driver'):continue
 rows[p.stem]=dict(module=p.stem,imports=re.findall(r'^import (\S+)',p.read_text(),re.M))
(E/'NLB_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows.values()))
(E/'NLB_IMPORT_CONFLICTS.json').write_text(json.dumps(conflicts,indent=2))
for path,name in [('evidence/axaudit2-20261102/NEP_WALKER.lean','NLB_READONLY_NEP_WALKER.lean.txt'),('evidence/slice-q-mul4-20261104/NFA_WALKER.lean','NLB_READONLY_NFA_WALKER.lean.txt')]:
 (E/name).write_bytes(subprocess.check_output(['git','show','HEAD:'+path]))
a=(E/'NLB_READONLY_NEP_WALKER.lean.txt').read_bytes();b=(E/'NLB_READONLY_NFA_WALKER.lean.txt').read_bytes()
(E/'NLB_WALKER_CONFORMANCE.json').write_text(json.dumps(dict(byte_identical=a==b,sha256=hashlib.sha256(a).hexdigest(),NFA_sha256=hashlib.sha256(b).hexdigest(),driver_diff_scope='module/root lists only; NKO memory/search-path runtime setup unchanged',fixtures='pending'),indent=2))
assert a==b
print(json.dumps(dict(roots=len(roots),groups=len(groups),import_conflicts=len(conflicts),walker_identical=a==b)))
