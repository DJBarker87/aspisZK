"""Own selector/runtime adaptation; retained ax2 walker is byte-identical."""
from pathlib import Path
import json,re,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;P=Path('evidence/tx2-common-20261110')
modules=sorted(p.stem for p in E.glob('NLT_*.lean') if not p.stem.endswith('Driver') and p.stem!='NLT_COMBINED_IMPORT')
combined=''.join('import '+m+'\n' for m in ['NLO_COMBINED_IMPORT','NLP_COMBINED_IMPORT','NLB_COMBINED_IMPORT','NKU_COMBINED_IMPORT','NLN_COMBINED_IMPORT',*modules])
combined+='set_option pp.proofs false\n#check AspisR1.RPx_Deployed.deployed\n#check NLT_CompleteRoot.root\n#print axioms AspisR1.RPx_Deployed.deployed\n#print axioms NLT_CompleteRoot.root\n'
(E/'NLT_COMBINED_IMPORT.lean').write_text(combined)
roots=[]
for m in modules:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)
 if ns:roots.extend(ns[1]+'.'+n for n in re.findall(r'^#print axioms (\w+)\s*$',s,re.M))
roots=list(dict.fromkeys(roots+['NLB_Parent.native_fold','NKU_ParentFold.source','NKU_ParentFold.cohort','NKU_ParentFold.clauses','NLN_TX2_053.root','AspisR1.RPx_Deployed.deployed']))
groups=[roots[i:i+12] for i in range(0,len(roots),12)]
(E/'NLT_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=2)+'\n')
for name in ['NLT_Driver','NLT_ProofDriver']:
 old=(P/(name.replace('NLT','NLP')+'.lean')).read_text();s=old.replace('NLP','NLT').replace('codex-cx-tx2-common-20261110','codex-cx-tx2-common2-20261110')
 if name.endswith('ProofDriver'):
  a=s.index('    else if mode == "proof0"');b=s.index('    else (#[], #[])',a)
  part=''.join('    else if mode == "proof'+str(i)+'" then\n      (#[`NLT_COMBINED_IMPORT], #['+', '.join('`'+r for r in group)+'])\n' for i,group in enumerate(groups))
  s=s[:a]+part+s[b:]
 (E/(name+'.lean')).write_text(s)
 (E/(name+'_DIFF.patch')).write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile=name.replace('NLT','NLP')+'.lean',tofile=name+'.lean')))
(E/'NLT_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:(E/'NLT_native'/n).write_bytes((P/'NLP_native'/n).read_bytes())
(E/'NLT_batch.py').write_text((P/'NLP_batch.py').read_text().replace('NLP','NLT'))
rows={}
for file in ['evidence/ledger22-20261110/NLO_EXPECTED_IMPORTS.jsonl','evidence/tx2-common-20261110/NLP_EXPECTED_IMPORTS.jsonl']:
 for line in Path(file).read_text().splitlines():
  r=json.loads(line)
  if r['module'] in rows:assert rows[r['module']]['imports']==r['imports'],r['module']
  rows[r['module']]=r
for p in E.glob('NLT_*.lean'):rows[p.stem]=dict(module=p.stem,imports=list(dict.fromkeys(([] if p.read_text().startswith('prelude') else ['Init'])+re.findall(r'^import (\S+)',p.read_text(),re.M))))
(E/'NLT_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows.values()))
a=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean'])
b=subprocess.check_output(['git','show','HEAD:evidence/slice-q-mul4-20261104/NFA_WALKER.lean']);assert a==b
(E/'NLT_WALKER_CONFORMANCE.json').write_text(json.dumps(dict(byte_identical=True,sha256=hashlib.sha256(a).hexdigest(),driver_diff_scope='module/root selectors and own runtime paths only; walker unchanged',fixtures='pending'),indent=2)+'\n')
print(json.dumps(dict(modules=len(modules),roots=len(roots),groups=len(groups),walker_identical=True)))
