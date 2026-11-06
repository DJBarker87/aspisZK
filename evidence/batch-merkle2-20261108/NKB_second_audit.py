"""Second and final combined import; first failure was a recorded own env omission."""
from pathlib import Path
import json,subprocess,sys,lzma
E=Path(__file__).resolve().parent
p=E/'NKB_IMPORT_PREFLIGHT.json';data=p.read_bytes() if p.exists() else lzma.decompress(p.with_name(p.name+'.xz').read_bytes());x=json.loads(data)
assert not x['missing'] and not x['unknown_expected_imports']
r=json.loads((E/'NKB_L048/receipt.json').read_text());assert r['exit_status']==0
history=[json.loads(t) for t in (E/'NKB_ATTEMPTS.jsonl').read_text().splitlines()];assert sum(t['module']=='NKB_COMBINED_IMPORT' and t['kind']=='lean' for t in history)==1
for n in [49,50,51]:
 a=f'NKB_L{n:03d}';r=subprocess.run([sys.executable,str(E/'NKB_run.py'),a])
 if r.returncode:print(a+' STOP; no third full combined import allowed',flush=True);raise SystemExit(r.returncode)
print('NKB second/final combined import, strict NFX scan and raw ax2 complete',flush=True)
