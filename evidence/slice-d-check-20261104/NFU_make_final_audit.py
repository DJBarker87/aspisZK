from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];roots=[];checked=[]
modules=['NFU_RecordGetters','NFU_AdapterGetters','NFU_PacketDomains','NFU_RowDomains','NFU_CompactLeaves','NFU_PrefixRecords','NFU_ZeroPort','NFU_TransportTag']
needed=set(modules)|{x['module']for x in json.loads((E/'NFU_RETARGET.json').read_text())}
for module in sorted(needed):
 p=E/(module+'.lean');digest=hashlib.sha256(p.read_bytes()).hexdigest();matching=[]
 for q in E.glob('NFU_L???/receipt.json'):
  x=json.loads(q.read_text())
  if x['module']==module and x['exit_status']==0 and digest in x['source_hashes'].values():matching.append(x)
 assert matching,module
 row=matching[-1];checked.append(dict(module=module,source_sha256=digest,attempt=row['attempt']))
 for text in row['print_axioms']:
  m=re.match(r"'([^']+)'",text)
  assert m and ('does not depend on any axioms' in text or set(re.search(r'\[([^]]*)\]',text)[1].split(', '))<={'propext','Classical.choice','Quot.sound'}),text
  if m[1] not in roots:roots.append(m[1])
(E/'NFU_STAGE2_ROOTS.json').write_text(json.dumps(roots,indent=1)+'\n');(E/'NFU_COMPILE_CLOSURE.json').write_text(json.dumps(checked,indent=1)+'\n')
(E/'NFU_STAGE2_IMPORT.lean').write_text('import NFQ_COMBINED_IMPORT\n'+'\n'.join('import '+m for m in modules)+'\n'+''.join('#print axioms '+r+'\n'for r in roots)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
base=(R/'evidence/slice-d-define-20261104/NFQ_ProofDriver.lean').read_text();start=base.index('    if mode == "proof0"');end=base.index('    else if mode == "fixtures"',start)
chunks=[roots[i:i+8]for i in range(0,len(roots),8)];code=''
for i,g in enumerate(chunks):code+=('    if'if i==0 else'    else if')+' mode == "stage2proof'+str(i)+'" then\n      (#[`NFU_STAGE2_IMPORT], #['+', '.join('`'+r for r in g)+'])\n'
s=(base[:start]+code+base[end:]).replace('NFQ','NFU');(E/'NFU_Stage2Driver.lean').write_text(s)
(E/'NFU_STAGE2_DRIVER.diff').write_text(''.join(difflib.unified_diff(base.splitlines(True),s.splitlines(True),fromfile='a/NFQ_ProofDriver.lean',tofile='b/NFU_Stage2Driver.lean')))
b=(E/'NFU_final_audit_batch.py').read_text().replace('NFU_L005','NFU_L059').replace('NFU_final_audit','NFU_stage2_audit').replace('NFU_ProofDriver','NFU_Stage2Driver').replace("[f'proof{i}' for i in range(1)]","[f'stage2proof{i}' for i in range("+str(len(chunks))+')]' )
(E/'NFU_stage2_audit_batch.py').write_text(b)
(E/'NFU_QUEUE_FINAL_AUDIT.json').write_text(json.dumps([dict(attempt=f'NFU_L{i:03}',kind=k,target=t,exit=0)for i,k,t in [(57,'lean','NFU_STAGE2_IMPORT'),(58,'lean','NFU_Stage2Driver'),(59,'auditbatch','NFU_Stage2Driver')]],indent=1)+'\n')
print(json.dumps(dict(modules=len(checked),raw_roots=len(roots),groups=len(chunks))))
