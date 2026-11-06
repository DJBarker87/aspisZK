from pathlib import Path
import subprocess,sys,json,hashlib,re
E=Path(__file__).resolve().parent
for row in (E/'NKR_ATTEMPTS.jsonl').read_text().splitlines():
 r=json.loads(row);m=r.get('module','');p=E/(m+'.lean')
 if r.get('kind')=='lean' and r['exit_status']==0 and p.exists() and r['source_hashes'].get(m+'.lean')==hashlib.sha256(p.read_bytes()).hexdigest():
  (E/(m+'.pass')).write_text(json.dumps(dict(attempt=r['attempt'],sha256=hashlib.sha256(p.read_bytes()).hexdigest())))
for a,m,needs in json.loads((E/sys.argv[1]).read_text()):
 needs=list(dict.fromkeys(needs+re.findall(r'^import (NKR_[\w.]+)',(E/(m+'.lean')).read_text(),re.M)))
 if any(not (E/(dep+'.pass')).exists() or json.loads((E/(dep+'.pass')).read_text())['sha256']!=hashlib.sha256((E/(dep+'.lean')).read_bytes()).hexdigest() for dep in needs):print(a+' skipped missing focused prerequisite',flush=True);continue
 subprocess.run([sys.executable,str(E/'NKR_make.py'),a,m],check=True)
 r=subprocess.run([sys.executable,str(E/'NKR_run.py'),a]);
 if r.returncode==0:(E/(m+'.pass')).write_text(json.dumps(dict(attempt=a,sha256=hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest())))
