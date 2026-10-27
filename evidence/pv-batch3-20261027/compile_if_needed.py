"""Reuse an exactly matching accepted focused module; never resend unchanged input."""
from pathlib import Path
import json,hashlib,re,subprocess,sys
from run import H
m=sys.argv[1];src=H/'lean'/(m.replace('.','/')+'.lean');sha=hashlib.sha256(src.read_bytes()).hexdigest()
env=json.loads((H/'env-J-private.json').read_text());search=[H/'lean-objects']+[Path(x) for x in env['LEAN_PATH'].split(':')];deps={}
for imp in re.findall(r'^import (\S+)',src.read_text(),re.M):
 p=next((x/(imp.replace('.','/')+'.olean') for x in search if (x/(imp.replace('.','/')+'.olean')).exists()),None)
 deps[imp]=dict(path=str(p) if p else None,sha256=hashlib.sha256(p.read_bytes()).hexdigest() if p else 'missing')
fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
t=json.loads((H/'TALLY.json').read_text())
for r in reversed(t['receipts']):
 if r['module']!=m or r['exit']!=0:continue
 rec=json.loads(Path(r['receipt']).read_text())
 if rec['source_sha256']==sha and rec['deps_fingerprint']==fp:
  print(json.dumps(dict(module=m,reused_attempt=r['attempt'],charged=False)),flush=True);sys.exit(0)
sys.exit(subprocess.run(['python3',str(H/'compile_lean.py'),m]).returncode)
