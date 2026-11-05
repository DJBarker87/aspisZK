from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
tasks=[('link','NGU_ProofDriver'),('link','NGU_Driver'),('audit','fixtures')]+[('audit',f'batch{i}') for i in range(26)]+[('audit','scan')]+[('lean',n) for n in json.loads((E/'NGU_STATEMENT_ROOTS.json').read_text())['modules']]
for kind,target in tasks:
 records=[json.loads(l) for l in (E/'NGU_ATTEMPTS.jsonl').read_text().splitlines()]
 # A successful immutable target is never rerun by resuming this queue.
 if any(x['kind']==kind and x['module']==target and x['exit_status']==0 for x in records):continue
 n=max([int(x['attempt'][-3:]) for x in records if x['attempt'].startswith('NGU_L')]+[0])+1
 assert n<=79,'reserve L080 for cache export'
 r=subprocess.run([sys.executable,str(E/'NGU_run.py'),f'NGU_L{n:03}',kind,target])
 if r.returncode:sys.exit(r.returncode)
