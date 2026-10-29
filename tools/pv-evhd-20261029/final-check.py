"""EXPERIMENTAL, NOT ADOPTED: final source/receipt check, no compiler rerun."""
from pathlib import Path
import ast, hashlib, json, re, subprocess
E=Path('evidence/pv-evhd-20261029')
modules=['PV_EVHD_Interface','PV_EVHD_Headline','PV_EVHD_Average','PV_EVHD_Residual']
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for m in modules:
 p=Path('lean/'+m+'.lean'); b=p.read_bytes(); s=b.decode()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|implemented_by)\b',s)
 assert 'maxRecDepth' not in s and 'maxHeartbeats' not in s
 for doc in re.findall(r'/--([\s\S]*?)-/',s): assert 'EXPERIMENTAL' in doc,(m,doc)
 rs=[json.loads(q.read_text()) for q in E.glob('receipt-*.json')]
 rs=[r for r in rs if r['target']==m and r['accepted'] and r['source_sha256']==sha(b)]
 assert rs,('no accepted current-source receipt',m)
 r=max(rs,key=lambda v:v['attempt'])
 out=(E/f"out-{r['attempt']}.log").read_text()
 assert r['exit']=='0' and r['admission']['allowed'] is True
 assert 'sorryAx' not in out and 'error:' not in out
 names=re.findall(r'^(?:private )?theorem (\w+)',s,re.M)
 for name in names:
  assert any("'"+m+'.'+name+"'" in a for a in r['axioms']),(m,name)
 for a in r['axioms']:
  match=re.search(r'depends on axioms: \[([^\]]*)\]',a)
  if match: assert set(match[1].replace(',',' ').split()) <= {'propext','Classical.choice','Quot.sound'}
 rows.append(dict(module=m,source_sha256=sha(b),receipt=r['attempt'],object_sha256=r['object_sha256'],theorems=names))
old=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean').read_text()
i=old.index('      (modelError',old.index('theorem privacy_headline_deployed'));j=old.index(')) ∧',i)
expr=old[i+7:j]
s=Path('lean/PV_EVHD_Headline.lean').read_text()
new=re.search(r'def bound : ℚ :=\n  (.*?)\n\n',s,re.S)[1]
assert expr.split()==new.split(),('bound expression changed',expr,new)
changes=subprocess.check_output(['git','diff','--name-only','e90651e952'],text=True).splitlines()
for p in changes:
 assert p.startswith(('lean/PV_EVHD_','tools/pv-evhd-20261029/','evidence/pv-evhd-20261029/')),p
for p in E.rglob('*'):
 if p.is_file(): assert p.stat().st_size<=20*1024*1024,p
# Exercise the actual source-only guard using the recorded failed-source hash.
code=Path('tools/pv-evhd-20261029/compile.py').read_text(); tree=ast.parse(code)
loop=next(n for n in tree.body if isinstance(n,ast.For) and ast.unparse(n.target)=='prior')
failures=[json.loads(q.read_text()) for q in E.glob('receipt-*.json')
 if not json.loads(q.read_text())['accepted']]
for failed in failures:
 try: exec(compile(ast.Module(body=[loop],type_ignores=[]),'guard-test','exec'),
   dict(E=E,json=json,source_sha=failed['source_sha256']))
 except AssertionError: pass
 else: raise AssertionError('failed-source guard did not refuse')
result=dict(experimental=True,adopted=False,modules=rows,exact_bound_tokens=True,
 protected_files_unchanged=True,failed_source_guard_test='PASS',failed_source_cases=len(failures),
 guard_sha256=sha(Path('tools/pv-evhd-20261029/compile.py').read_bytes()),
 source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(E/'final-manifest.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
