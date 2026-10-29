"""Upload one own source and run one admitted focused attempt, preserving input."""
from pathlib import Path
import subprocess,sys,json,hashlib
E=Path(__file__).resolve().parent;D='/home/dombarker/project-offloads/codex-pv-diag2-20261029';host='dombarker@100.108.41.90'
n,module=sys.argv[1:];assert 63000<=int(n)<=63099
p=E/(module+'.lean');b=p.read_bytes();snapshot=E/f'lean{n}-source.lean.txt';assert not snapshot.exists();snapshot.write_bytes(b)
(E/f'lean{n}-input.json').write_text(json.dumps(dict(module=module,attempt=int(n),revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(b).hexdigest(),source_snapshot=snapshot.name,dirty_source=True),indent=2)+'\n')
subprocess.run(['scp',str(p),host+':'+D+'/sources/'+module+'.lean'],check=True)
r=subprocess.run(['ssh',host,'python3 '+D+'/resume-run.py lean'+n+' privatelean '+n+' '+module])
raise SystemExit(r.returncode)
