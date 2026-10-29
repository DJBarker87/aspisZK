"""Freeze only compiled development statements; then generate reserved audits."""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-ownc-20261029'
checked={}
for p in E.glob('lean-*/receipt.json'):
 j=json.loads(p.read_text())
 if j['exit']==0:checked[j['module'].replace('/','.')]=j
roots=[];modules=[];manifest=[]
for p in sorted(L.glob('PV_OWNC_*.lean')):
 if any(x in p.stem for x in ['Audit','Replay']):continue
 m='R1Z.'+p.stem;s=p.read_text();sha=hashlib.sha256(p.read_bytes()).hexdigest()
 assert m in checked and checked[m]['source_sha256']==sha,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 th=re.findall(r'^\s*theorem\s+(\w+)',s,re.M)
 roots.extend(ns+'.'+t for t in th);modules.append(m)
 manifest.append(dict(module=m,path=str(p.relative_to(R)),sha256=sha,blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),attempt=checked[m]['attempt']))
assert len(roots)==len(set(roots))
s=''.join('import '+m+'\n' for m in modules)+'set_option autoImplicit false\n'
s+='\n'.join('#check '+r for r in roots)+'\n'
for r in ['R1Z.PV_OWNC_InPlaceResult.guarded','R1Z.PV_OWNC_GuardCleanup.original_layout','R1Z.PV_OWNC_LinkPush.forest','R1Z.PV_OWNC_FlatMap.initialized','R1Z.PV_OWNC_CursorVector.initialized']:
 s+='#print '+r+'\n#print axioms '+r+'\n'
(L/'PV_OWNC_StatementsAudit.lean').write_text(s)
(L/'PV_OWNC_AxiomsAudit.lean').write_text('import R1Z.PV_OWNC_StatementsAudit\n'+'\n'.join('#print axioms '+r for r in roots)+'\n')
s=(E/'unsubmitted/PV_OWNC_OwnershipStages.lean.txt').read_text().replace('import R1Z.PV_OWNC_EmptyVector','import R1Z.PV_OWNC_AxiomsAudit').replace('R1Z.PV_OWNC_OwnershipStages','R1Z.PV_OWNC_FocusedReplay')
(L/'PV_OWNC_FocusedReplay.lean').write_text(s)
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=manifest,roots=roots,scope='development model closure; no complete source K-1 gate or privacy endpoint claim'),indent=2)+'\n')
(E/'audit-targets.txt').write_text('62897 R1Z/PV_OWNC_StatementsAudit\n62898 R1Z/PV_OWNC_AxiomsAudit\n62899 R1Z/PV_OWNC_FocusedReplay\n')
print('frozen development modules',len(modules),'theorems',len(roots))
