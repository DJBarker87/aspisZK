from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;env=json.loads((E/'NNG_ENV.json').read_text());groups=json.loads((E/'NNG_C136_AUDIT_ROOTS.json').read_text())['groups']
modes=['fixtures']+['proof'+str(i)for i in range(1,len(groups))]
for n,mode in enumerate(modes,363):
 a='NNG_L'+str(n);assert not(E/a/'receipt.json').exists()
 x=dict(attempt=a,kind='audit',module=mode+' own new roots',sources=['NNG_C136_audit_batch.py','NNG_C136_AUDIT_ROOTS.json','NNG_C136_AUDIT_MODULES.json','NNG_C136_AUDIT_MANIFEST_PINS.json'],command=['python3','NNG_C136_audit_batch.py',mode],timeout=180,env=env,expected_time='Raw ax2 traversal of own new roots, <=24 per group; previous53 roots excluded',audit_combined='NNG_CANDIDATE_COMBINED',audit_modules=['NNG_C136_ProofDriver'],collect_globs=['NNG_C136_audit/'+mode+'/*'])
 (E/(a+'.json')).write_text(json.dumps(x,indent=1))
 r=subprocess.run([sys.executable,str(E/'NNG_run.py'),a])
 if r.returncode:raise SystemExit(r.returncode)
