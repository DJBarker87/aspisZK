from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownm-20261029'
selected={}
for task in ['owni','ownj','ownk','ownl']:
 p=R/f'evidence/pv-{task}-20261029/focused-dependencies.json'
 if p.exists():
  for r in json.loads(p.read_text())['order']:selected[r['module'].replace('.','/')]=r
 p=R/f'evidence/pv-{task}-20261029/final-fingerprint.json'
 for r in json.loads(p.read_text())['rows']:selected[r['module'].replace('.','/')]=r
old=json.loads((R/'evidence/pv-ownc-20261029/final-fingerprint.json').read_text())['rows']
external=json.loads((R/'evidence/pv-world-20261028/external-object-manifest.json').read_text())
ready={r['module'].replace('.','/') for r in old+external}|{'R1Z/ProverRwFullExternalTypes','R1Z/ProverRwFullTypes'}
order=[];seen=set()
def visit(m):
 m=m.replace('.','/')
 if m in ready or m in seen:return
 assert m in selected,m
 r=selected[m];p=R/r['source_path'];b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==r['source_sha256'],m
 seen.add(m)
 for d in re.findall(r'^import (\S+)',b.decode(),re.M):visit(d)
 order.append(dict(module=m,source_path=r['source_path'],source_sha256=hashlib.sha256(b).hexdigest(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+r['source_path']],text=True).strip(),authority='inherited recorded resolution; unchanged source at current HEAD'))
for m in ['R1Z.PV_OWNK_ConcreteDecoder','R1Z.PV_OWNL_RowEnumeration','R1Z.PV_OWNL_PrefixProduct','R1Z.PV_OWNL_Suffix']:visit(m)
# Keep launcher's other admitted module metadata as well.
for r in json.loads((E/'focused-dependencies.json').read_text())['order']:
 selected[r['module']]=r
for r in order:selected[r['module']]=r
(E/'focused-dependencies.json').write_text(json.dumps(dict(order=list(selected.values())),indent=2)+'\n')
(E/'dense-dependency-queue.txt').write_text(''.join(f'{65905+i} {r["module"]}\n'for i,r in enumerate(order)))
print(len(order),'focused dependencies',65905+len(order)-1)
