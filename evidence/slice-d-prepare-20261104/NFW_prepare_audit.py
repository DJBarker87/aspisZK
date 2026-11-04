from pathlib import Path
import json,re,difflib,hashlib
E=Path(__file__).resolve().parent;Q=E.parent/'slice-d-define-20261104'
mods=['NFW_LPi_TowerValues','NFW_LPi_PowersStep','NFW_LPi_PowersPrefix','NFW_LPi_PowersValue','NFW_LPi_PowersSource','NFW_LPm_PowersBridge','NFW_NBQ_Powers29','NFW_PowersFrame','NFW_PowersDomain','NFW_PowersInjective','NFW_PowersCohort']
roots=[]
for m in mods:
 s=(E/(m+'.lean')).read_text();namespace=re.search(r'^namespace (.+)',s,re.M)[1]
 roots.extend(namespace+'.'+t for t in re.findall(r'^theorem (\w+)',s,re.M))
(E/'NFW_AUDIT_ROOTS.json').write_text(json.dumps(roots,indent=1)+'\n')
(E/'NFW_COMBINED_IMPORT.lean').write_text('\n'.join('import '+m for m in mods)+'\nimport NFQ_STAGE2_IMPORT\nimport NFS_QueryLoopRoot\n'+'\n'.join('#print axioms '+r for r in roots)+'\n#print axioms AspisR1.RPx_Deployed.deployed\n')
s=(Q/'NFQ_ProofDriver.lean').read_text();a=s.index('    if mode == "proof0"');b=s.index('    else if mode == "fixtures"',a)
groups=[roots[i:i+8] for i in range(0,len(roots),8)]
new=''
for i,g in enumerate(groups):new+=('    if' if i==0 else '    else if')+' mode == "proof'+str(i)+'" then\n      (#[`NFW_COMBINED_IMPORT], #['+', '.join('`'+r for r in g)+'])\n'
driver=s[:a]+new+s[b:]
(E/'NFW_ProofDriver.lean').write_text(driver)
(E/'NFW_DRIVER.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),driver.splitlines(True),fromfile='a/NFQ_ProofDriver.lean',tofile='b/NFW_ProofDriver.lean')))
walker=(E.parent/'axaudit2-20261102/NEP_WALKER.lean').read_bytes()
assert walker==(Q/'NFQ_WALKER_SOURCE.lean.txt').read_bytes()
(E/'NFW_WALKER_SOURCE.lean.txt').write_bytes(walker)
(E/'NFW_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 (E/'NFW_native'/n).write_bytes((Q/'NFQ_L010/sources/NFQ_native'/n).read_bytes())
(E/'NFW_AUDIT_BUILD_PINS.json').write_text(json.dumps({'walker_sha256':hashlib.sha256(walker).hexdigest(),'reference':'evidence/axaudit2-20261102/NEP_WALKER.lean','walker_byte_identical':True,'adaptation':'driver root and module lists only; runtime/memory/walker unchanged','groups':len(groups),'roots':len(roots)},indent=1)+'\n')
batch=(Q/'NFQ_final_audit_batch.py').read_text().replace('NFQ','NFW').replace("(B/'NFW_L010.json')","(B/sys.argv[1])").replace("parent_attempt='NFW_L010'","parent_attempt=parent['attempt']").replace('range(2)','range('+str(len(groups))+')')
(E/'NFW_final_audit_batch.py').write_text(batch)
p=E/'NFW_run.py';s=p.read_text();s=s.replace("command=['python3','NFW_final_audit_batch.py']","command=['python3','NFW_final_audit_batch.py',a+'.json']")
a=" files['NFW_final_audit_batch.py']=(E/'NFW_final_audit_batch.py').read_text()"
s=s.replace(a,a+"\n for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NFW_native/'+n]=(E/'NFW_native'/n).read_text()")
s=s.replace("for name in ['NFW_Driver','NFW_ProofDriver','NFW_Stage2Driver']:","for name in ['NFW_Driver','NFW_ProofDriver','NFW_Stage2Driver']:")
p.write_text(s)
print('audit roots',len(roots),'groups',len(groups))
