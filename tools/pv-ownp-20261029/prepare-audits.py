from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownp-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
receipts=[json.loads(p.read_text())for p in sorted(E.glob('lean-*/receipt.json'))]
rows=[];decls=[]
for p in sorted(L.glob('PV_OWNP_*.lean')):
 if any(s in p.stem for s in ['Audit','Replay']):continue
 b=p.read_bytes();m='R1Z.'+p.stem
 accepted=[r for r in receipts if r['module']==m.replace('.','/') and r['source_sha256']==hashlib.sha256(b).hexdigest() and r['exit']==0]
 assert accepted,('uncompiled current source',m)
 ds=[m+'.'+x for x in re.findall(r'^theorem\s+(\w+)',b.decode(),re.M)]
 assert all('#print axioms '+d.rsplit('.',1)[1] in b.decode() for d in ds)
 decls+=ds;rows.append(dict(module=m,source_path=str(p.relative_to(R)),source_sha256=hashlib.sha256(b).hexdigest(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),statements=ds,accepted_attempt=accepted[-1]['attempt']))
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(modules=rows,statement_count=len(decls),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),classification='error-preserving helper and actual-input source-stage composition; deployed link installation remains separately audited'),indent=2)+'\n')
imports=''.join('import '+r['module']+'\n'for r in rows)
links=['ActualInput','SourceDense','Transcript879','Transcript890','OwnedPublicPlan']
(L/'PV_OWNP_StatementsAudit.lean').write_text(imports+'set_option pp.proofs false\n'+''.join('#print '+d+'\n'for d in decls)+''.join('#print R1Z.PV_OWNM_V239.PV_OWNM_Link_'+n+'\n'for n in links)+'#print R1Z.PV_OWNM_V239.ResourceExit\n#print R1Z.PV_OWNM_V239.attach\n#print R1Z.PV_OWNM_V239.restore\n')
(L/'PV_OWNP_AxiomsAudit.lean').write_text('import R1Z.PV_OWNP_StatementsAudit\n'+''.join('#print axioms '+d+'\n'for d in decls)+'#print axioms R1Z.PV_OWNM_V239.restore\n')
(L/'PV_OWNP_FocusedReplay.lean').write_text('import R1Z.PV_OWNP_AxiomsAudit\n'+''.join('#check '+d+'\n'for d in decls))
(E/'audit-queue.txt').write_text('67297 R1Z/PV_OWNP_StatementsAudit\n67298 R1Z/PV_OWNP_AxiomsAudit\n67299 R1Z/PV_OWNP_FocusedReplay\n')
print(len(rows),'modules',len(decls),'new statements')
