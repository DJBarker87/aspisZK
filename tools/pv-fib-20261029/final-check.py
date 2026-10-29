"""Final own-manifest/source/axioms audit; no unchanged Lean replay."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path('evidence/pv-fib-20261029');receipts=[json.load(open(p)) for p in sorted(E.glob('receipt-*.json'))]
accepted={}
for r in receipts:
 assert 67500<=r['attempt']<=67596
 assert r['admission']['allowed'] is True
 if r['accepted']:accepted[r['target']]=r
checks=[]
for module in ['PV_FIB_Restricted','PV_FIB_Termination']:
 source=Path('lean/'+module+'.lean').read_bytes();r=accepted[module]
 assert hashlib.sha256(source).hexdigest()==r['source_sha256']
 names=re.findall(r'^theorem (\w+)',source.decode(),re.M)
 for name in names:
  lines=[x for x in r['axioms'] if "'"+module+'.'+name+"'" in x]
  assert len(lines)==1,(module,name)
  assert all(x not in lines[0] for x in ['sorryAx','Lean.ofReduceBool'])
  ax=re.search(r'depends on axioms: \[([^\]]*)\]',lines[0])
  if ax:assert set(ax[1].split(', '))<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|^axiom |set_option max',source.decode(),re.M)
 checks.append(dict(module=module,sha256=hashlib.sha256(source).hexdigest(),receipt=r['attempt'],theorems=names,axioms=r['axioms']))
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
(E/'final-manifest.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),checks=checks,lean_attempts=len(receipts),native_scopes=0,kani=0,audit_ids_used=[],release_claim=False,limitations='Source/control-flow clock obstruction and conditional model theorems; no deployed non-bad native pair or complete failure/divergence association.'),indent=2)+'\n')
print('PASS own frozen targets, axioms, source hashes, sizes; no endpoint closure claim')
