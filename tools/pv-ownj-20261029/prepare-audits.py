from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-ownj-20261029'
files=sorted(p for p in L.glob('PV_OWNJ_*.lean') if not any(x in p.name for x in ['Audit','Replay']))
names=[]
for p in files:
 s=p.read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 for name in re.findall(r'^theorem (\w+)',s,re.M):names.append(ns+'.'+name)
imports=''.join('import R1Z.'+p.stem+'\n' for p in files)
(L/'PV_OWNJ_StatementsAudit.lean').write_text(imports+'\n'+''.join('#check @'+n+'\n'for n in names)+''.join('#print '+n+'\n' for n in ['R1Z.PV_OWNJ_ValueBridge.value_commutes','R1Z.PV_OWNJ_Claims.built_lengths','R1Z.PV_OWNJ_FiatShamir.replay_append','R1Z.PV_OWNJ_PublicInstance.callback_public']))
(L/'PV_OWNJ_AxiomsAudit.lean').write_text('import R1Z.PV_OWNJ_StatementsAudit\n'+''.join('#print axioms '+n+'\n'for n in names))
records=[dict(module='R1Z/'+p.stem,source_path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in files]
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(development=records,theorems=names,audits=[dict(attempt=64797,module='R1Z/PV_OWNJ_StatementsAudit'),dict(attempt=64798,module='R1Z/PV_OWNJ_AxiomsAudit'),dict(attempt=64799,module='R1Z/PV_OWNJ_FocusedReplay')],scope='one final focused new-source closure replay; not endpoint or release theorem'),indent=2)+'\n')
print(len(files),'development modules',len(names),'named theorems')
