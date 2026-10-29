from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownl-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
names=['Scale','HelperSlots','HelperRows','InputBytes','SampleWord','SampleCanon','Inputs','RowEnumeration','Suffix','PrefixProduct']
rows=[];decls=[]
for n in names:
 p=L/('PV_OWNL_'+n+'.lean');b=p.read_bytes();m='R1Z.PV_OWNL_'+n
 ds=[m+'.'+x for x in re.findall(r'^theorem\s+(\w+)',b.decode(),re.M)];decls+=ds
 assert all('#print axioms '+d.rsplit('.',1)[1] in b.decode() for d in ds)
 receipts=[json.loads(p.read_text())for p in E.glob('lean-*/receipt.json')]
 accepted=[j for j in receipts if j['module']==m.replace('.','/') and j['source_sha256']==hashlib.sha256(b).hexdigest() and j['exit']==0]
 assert accepted,m
 rows.append(dict(module=m,source_path=str(p.relative_to(R)),source_sha256=hashlib.sha256(b).hexdigest(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),statements=ds,accepted_attempt=accepted[-1]['attempt']))
manifest=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=rows,statement_count=len(decls),classification='local mathematical and source-shaped invariant results; not V239 restoration')
(E/'frozen-proof-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
imports=''.join('import '+r['module']+'\n' for r in rows)
key=['Inputs.accepted_columns','Inputs.statement_points_canon','SampleCanon.sample_canonical','HelperRows.vector_canonical','RowEnumeration.dense_sparse','Suffix.scanner_decoded','PrefixProduct.prefix_weight']
(L/'PV_OWNL_StatementsAudit.lean').write_text(imports+'set_option autoImplicit false\n'+''.join('#check '+d+'\n' for d in decls)+''.join('#print R1Z.PV_OWNL_'+d+'\n' for d in key)+'#print R1Z.PV_OWNK_TowerCanon.Canon\n#print R1Z.PV_OWNL_HelperSlots.slot\n#print R1Z.PV_OWNL_HelperRows.vector\n')
(L/'PV_OWNL_AxiomsAudit.lean').write_text('import R1Z.PV_OWNL_StatementsAudit\n'+''.join('#print axioms '+d+'\n' for d in decls))
(L/'PV_OWNL_FocusedReplay.lean').write_text('import R1Z.PV_OWNL_AxiomsAudit\n'+''.join('#print axioms R1Z.PV_OWNL_'+d+'\n' for d in key))
(E/'audit-queue.txt').write_text('65697 R1Z/PV_OWNL_StatementsAudit\n65698 R1Z/PV_OWNL_AxiomsAudit\n65699 R1Z/PV_OWNL_FocusedReplay\n')
print(len(rows),'modules;',len(decls),'local statements; no theorem added by audit modules')
