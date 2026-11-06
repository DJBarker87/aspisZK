from pathlib import Path
import sys,subprocess,hashlib,json,shutil
b=Path.cwd();mode=sys.argv[1];attempt=sys.argv[2];work=b/'PCC_final_audits'/attempt;work.mkdir(parents=True,exist_ok=False)
for name in ['PCC_AUDIT_ROOTS.json','PCC_AUDIT_MODULES.json','PCC_EXPECTED_IMPORTS.jsonl']:
 shutil.copyfile(b/name,work/name)
binary=b/'PCC_native/PCC_ProofDriver';before=hashlib.sha256(binary.read_bytes()).hexdigest()
r=subprocess.run([str(binary),mode],cwd=work)
after=hashlib.sha256(binary.read_bytes()).hexdigest();assert before==after
(work/'PCC_binary.json').write_text(json.dumps(dict(binary=str(binary),before=before,after=after,unchanged=True,exit=r.returncode,mode=mode)))
sys.exit(r.returncode)
