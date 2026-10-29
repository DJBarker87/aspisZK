from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownh-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
mods=['PV_OWNH_Address','PV_OWNH_Literals'];roots=[];manifest=[]
for m in mods:
 p=L/(m+'.lean');b=p.read_bytes();s=b.decode()
 receipts=[json.loads(x.read_text()) for x in E.glob('lean-*/receipt.json')]
 receipt=next(r for r in receipts if r.get('module')=='R1Z/'+m and r['exit']==0 and r['source_sha256']==hashlib.sha256(b).hexdigest())
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 roots.extend(ns+'.'+t for t in re.findall(r'^theorem (\w+)',s,re.M))
 manifest.append(dict(module='R1Z.'+m,path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),attempt=receipt['attempt']))
# Single final frozen dependency manifest, replayed only once. The focused
# dependency recompiles already establish each target before these audits.
manifest.extend(dict(module=r['module'].replace('/','.'),path=r['source_path'],sha256=r['source_sha256'],attempt=r['attempt']) for r in receipts if r['exit']==0 and 'PV_OWNH_' not in r['module'])
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(modules=manifest,roots=roots,scope='V229/V230 model/literal/resource closure plus source-argument algebra; no privacy-endpoint replay'),indent=2)+'\n')
checks='\n'.join('#check '+r for r in roots)+'\n'
text=''.join('import R1Z.'+m+'\n' for m in mods)+checks
for r in ['R1Z.PV_OWNH_Literals.v229_result','R1Z.PV_OWNH_Literals.v229_selected','R1Z.PV_OWNH_Literals.v229_selected_values','R1Z.PV_OWNH_Literals.v230_result','R1Z.PV_OWNH_Literals.request_layouts']:
 text+='#print '+r+'\n'
(L/'PV_OWNH_StatementsAudit.lean').write_text(text)
(L/'PV_OWNH_AxiomsAudit.lean').write_text('import R1Z.PV_OWNH_StatementsAudit\n'+'\n'.join('#print axioms '+r for r in roots)+'\n')
(L/'PV_OWNH_FocusedReplay.lean').write_text('import R1Z.PV_OWNH_AxiomsAudit\n'+''.join('import '+m['module']+'\n' for m in manifest)+checks)
(E/'audit-targets.txt').write_text('63897 R1Z/PV_OWNH_StatementsAudit\n63898 R1Z/PV_OWNH_AxiomsAudit\n63899 R1Z/PV_OWNH_FocusedReplay\n')
print(len(manifest),'frozen targets;',len(roots),'new theorems')
