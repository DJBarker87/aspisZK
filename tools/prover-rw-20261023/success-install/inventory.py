"""Read-only retained-body inventory for successful proof-body operations."""
from pathlib import Path
import re,json,subprocess,hashlib
r=Path(__file__).resolve().parents[3]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023'
x=json.loads((e/'native-install/remaining-obligations.json').read_text())
ids=set(x['components'][0]['still_uninstalled_reference_ids'])
s=(r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean').read_text()
names={int(m[2]):m[1] for m in re.finditer(r'^abbrev (\S+) .*?ExternalFuns.op(\d+)',s,re.M) if int(m[2]) in ids}
variants={i:[n,n.removeprefix('aspis_core.').removeprefix('aspis_statement.')] for i,n in names.items()}
pattern=r'(?m)^def\s+(?:'+ '|'.join(re.escape(n) for ns in variants.values() for n in ns)+r')\b'
p=subprocess.run(['rg','-l','-U',pattern,'docs/research/100bit-spend-path-20261013','--glob','*.lean'],cwd=r,capture_output=True,text=True)
found={i:[] for i in names}
for rel in p.stdout.splitlines():
 text=(r/rel).read_text()
 for i,n in names.items():
  m=next((m for v in variants[i] if (m:=re.search(r'^def\s+'+re.escape(v)+r'(?=\s|\{)',text,re.M))),None)
  if not m:continue
  end=text.find('\n/--',m.end())
  if end<0:continue
  b=text[m.start():end].strip()
  if '\nend ' in b or len(b)>100000:continue
  found[i].append(dict(path=rel,lines=b.count('\n')+1,sha256=hashlib.sha256(b.encode()).hexdigest(),declaration=n))
for i in found:found[i].sort(key=lambda x:(x['lines'],x['path']))
(e/'success-install/retained-body-inventory.json').write_text(json.dumps(found,indent=2)+'\n')
for i,n in names.items():print(i,n,[(p['lines'],p['path']) for p in found[i][:2]])
