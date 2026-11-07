from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;env=json.loads((E/'NNG_ENV.json').read_text())
modes=['fixtures']+['proof'+str(i) for i in range(len(json.loads((E/'NNG_FOLD_AUDIT_ROOTS.json').read_text())['groups']))]
for i,mode in enumerate(modes,217):
 a='NNG_L'+str(i);assert not (E/a/'receipt.json').exists()
 x=dict(attempt=a,kind='audit',module=mode,sources=['NNG_FOLD_audit_batch.py','NNG_FOLD_AUDIT_ROOTS.json','NNG_FOLD_AUDIT_MODULES.json','NNG_FOLD_AUDIT_MANIFEST_PINS.json'],command=['python3','NNG_FOLD_audit_batch.py',mode],timeout=180,env=env,expected_time='Raw ax2 traversal of own focused source-fold roots; four roots at most',audit_combined='NNG_FOLD_COMBINED',audit_modules=['NNG_FOLD_ProofDriver'],collect_globs=['NNG_FOLD_audit/'+mode+'/*'])
 (E/(a+'.json')).write_text(json.dumps(x,indent=1))
 r=subprocess.run([sys.executable,str(E/'NNG_run.py'),a])
 if r.returncode:raise SystemExit(r.returncode)
