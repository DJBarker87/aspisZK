from auditlib8 import *
pf=json.loads((P/'pins.json').read_text());pf['branches']['fscan']='codex/pv-fscan-20261028';pf['revisions']['fscan']=subprocess.check_output(['git','rev-parse','codex/pv-fscan-20261028'],text=True).strip();pins.update(pf['revisions']);(P/'pins.json').write_text(json.dumps(pf,indent=2)+'\n')
for p in ['SCAN.md','CLASSIFY.md','selected-rows.json','classification/draft-rows.json','classification/validation.json','classification/source-corrections.json']:
 read('fscan','evidence/pv-fscan-20261028/'+p)
# Worker-final statements and raw receipts with metrics and wrapped axiom output.
receipts=[]
sets={'pv-rdb1-20261028':['54738-receipt.json','54739-receipt.json'],
'pv-rdb2-20261028':['lean-41198/receipt.json','lean-41199/receipt.json'],
'pv-rdcd-20261028':['lean-41466/receipt.json','lean-41494/receipt.json','lean-41495/receipt.json','lean-41496/receipt.json','lean-41499/receipt.json'],
'pv-rdb2c-20261028':['lean-60598/receipt.json','lean-60599/receipt.json'],
'pv-rdeac-20261028':['receipt-61101.json','receipt-61197.json','receipt-61198.json','receipt-61199.json']}
for job,paths in sets.items():
 for tail in paths:
  path='evidence/'+job+'/'+tail;s=read('rw',path)
  if s is None:continue
  x=json.loads(s);minimal={k:v for k,v in x.items() if k not in ['deployed_configuration','target','axioms']};minimal.update(job=job,path=path,ref='rw',target=x.get('module',x.get('target')),axioms=x.get('axioms'))
  receipts.append(minimal)
for k,job in [('rdb2d','pv-rdb2d-20261028'),('rdcd3','pv-rdcd3-20261028'),('rjdec','pv-rjdec-20261028')]:
 for tail in ['REPORT.md','STATUS.json','summary.json','combined-audit.json']:read(k,'evidence/'+job+'/'+tail)
# Complete worker restoration packets and their source gates, not just lead summaries.
for job in ['pv-rdb1-20261028','pv-rdb2-20261028','pv-rdcd-20261028','pv-rdb2c-20261028']:
 paths=subprocess.check_output(['git','ls-tree','-r','--name-only',pins['rw'],'evidence/'+job],text=True).splitlines()
 for path in paths:
  if path.endswith('.json') and not any(t in path for t in ['metadata','unit-graph','receipt.json','admission','barrier','reservation','source-snapshots']):
   size=int(subprocess.check_output(['git','cat-file','-s',pins['rw']+':'+path],text=True))
   if size<1500000:read('rw',path)
# rdeac literal diagnostic provenance and failed replay/void repair.
for p in ['diagnostic-provenance.json','pending-replay.json','summary.json','attempts.json','REPORT.md']:
 read('rw','evidence/pv-rdeac-20261028/'+p)
# Stream A evidence as committed source, never its objects.
for glob in ['evidence/native-reconcile-20261028/NDO_HANDOFF.md','evidence/native-chainassoc-20261028/NDQ_CHAIN_ASSOCIATION.md','evidence/native-sbfstack-20261028/NDC_STACK_FINDING.md','evidence/kani-diag2-20261028/KNB_FINDING.md','evidence/kani-diag3-20261028/KNC_FINDING.md','evidence/kani-k2leaf-20261028/KNF_FINDING.md','docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md']:
 read('research',glob)
# Every historical closing statement re-read on candidate/research; preserve scoped original witnesses.
rs=json.loads((B/'recount7/rows7.json').read_text());closing=[]
for r in rs:
 th=r.get('closure_theorem') if r['recount7_status']=='CLOSED-ON-CANDIDATE' else r.get('theorem','') if r['recount7_status']=='CLOSED-ON-RESEARCH' else None
 if not th:continue
 for w in r.get('closure_statements7',[]):
  for k in ['rw','research']:
   s=read(k,w['path'])
   if s is not None:closing.append(dict(id=r['id'],theorem=th,ref=k,path=w['path'],sha256=hashlib.sha256(s.encode()).hexdigest(),same_as7=hashlib.sha256(s.encode()).hexdigest()==w['sha256']))
(P/'closing-statements8.json').write_text(json.dumps(closing,indent=1)+'\n')
(P/'receipt-audit8.json').write_text(json.dumps(receipts,indent=1)+'\n')
(P/'manifest.json').write_text(json.dumps(manifest,indent=1)+'\n')
print('Supplement',len(manifest),'witnesses;',len(receipts),'final raw receipts;',len(closing),'closing statement associations')
