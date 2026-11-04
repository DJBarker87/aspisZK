from pathlib import Path
import re,json,difflib
E=Path('evidence/slice-d-define-20261104')
mods=['NFQ_FieldLaws','NFQ_FieldPorts','NFQ_Readonly','NFQ_Reduce','NFQ_PreparedMultiplier','NFQ_StatementLaws','NFQ_WideGetters','NFQ_Linear','NFQ_ZeroPrimitives','NFQ_ZeroGateModel','NFQ_ZeroSuccess','NFQ_ZeroReference','NFQ_ZeroSource','NFQ_FieldDomains','NFQ_PreparedDomain','NFQ_StatementDomains']
if json.loads((E/'NFQ_L047/receipt.json').read_text())['exit_status']==0:mods+=['NFQ_ZeroStep']
roots=[]
for m in mods:
 s=(E/(m+'.lean')).read_text();roots += [m+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
(E/'NFQ_STAGE2_ROOTS.json').write_text(json.dumps(roots,indent=1)+'\n')
(E/'NFQ_STAGE2_IMPORT.lean').write_text('\n'.join('import '+m for m in mods)+'\n'+ '\n'.join('#print axioms '+r for r in roots)+'\n#print axioms AspisR1.RPx_Deployed.deployed\n')
s=(E/'NFQ_ProofDriver.lean').read_text();start=s.index('    if mode == "proof0"');end=s.index('    else if mode == "fixtures"',start)
chunks=[roots[i:i+8] for i in range(0,len(roots),8)]
code=''
for i,g in enumerate(chunks):
 code+=('    if' if i==0 else '    else if')+' mode == "stage2proof'+str(i)+'" then\n      (#[`NFQ_STAGE2_IMPORT], #['+', '.join('`'+r for r in g)+'])\n'
s2=s[:start]+code+s[end:];(E/'NFQ_Stage2Driver.lean').write_text(s2)
(E/'NFQ_STAGE2_DRIVER.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),s2.splitlines(True),fromfile='a/NFQ_ProofDriver.lean',tofile='b/NFQ_Stage2Driver.lean')))
b=(E/'NFQ_final_audit_batch.py').read_text().replace('NFQ_L010','NFQ_L050').replace('NFQ_final_audit','NFQ_stage2_audit').replace('NFQ_ProofDriver','NFQ_Stage2Driver').replace("[f'proof{i}' for i in range(2)]","[f'stage2proof{i}' for i in range("+str(len(chunks))+')]' )
(E/'NFQ_stage2_audit_batch.py').write_text(b)
p=E/'NFQ_run.py';r=p.read_text().replace("'NFQ_ProofDriver','NFA_WALKER'","'NFQ_ProofDriver','NFQ_Stage2Driver','NFA_WALKER'")
a="elif kind=='auditbatch':\n files['NFQ_final_audit_batch.py']=(E/'NFQ_final_audit_batch.py').read_text()"
b="elif kind=='auditbatch' and target=='NFQ_Stage2Driver':\n files['NFQ_stage2_audit_batch.py']=(E/'NFQ_stage2_audit_batch.py').read_text()\n sources=['NFQ_generated/NFQ_Stage2Driver.lean','NFQ_stage2_audit_batch.py','NFQ_native/NFQ_Stage2Driver.c','NFQ_native/NFA_WALKER.c','NFQ_native/NFA_MemoryLimit.c']\n command=['python3','NFQ_stage2_audit_batch.py']\nelif kind=='auditbatch':\n files['NFQ_final_audit_batch.py']=(E/'NFQ_final_audit_batch.py').read_text()"
assert a in r;r=r.replace(a,b)
r=r.replace("(['NFQ_COMBINED_IMPORT'] if x['kind']=='auditbatch' else [])","(['NFQ_STAGE2_IMPORT' if x['module']=='NFQ_Stage2Driver' else 'NFQ_COMBINED_IMPORT'] if x['kind']=='auditbatch' else [])")
r=r.replace("in ['NFQ_Driver','NFQ_ProofDriver','fixtures']","in ['NFQ_Driver','NFQ_ProofDriver','NFQ_Stage2Driver','fixtures']")
r=r.replace("(b/'NFQ_final_audit').rglob('*')","(b/('NFQ_stage2_audit' if {target!r}=='NFQ_Stage2Driver' else 'NFQ_final_audit')).rglob('*')")
r=r.replace("for name in ['NFQ_Driver','NFQ_ProofDriver']:","for name in ['NFQ_Driver','NFQ_ProofDriver','NFQ_Stage2Driver']:")
p.write_text(r)
print(len(roots),len(chunks))
