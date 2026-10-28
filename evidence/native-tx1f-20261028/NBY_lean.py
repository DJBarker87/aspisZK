"""Own single-module submission using unchanged S2W scoped runner."""
from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBY_host as h
R=E.parents[1];a=sys.argv[1];module=sys.argv[2];p=R/'docs/research/100bit-spend-path-20261013/lean'/f'{module}.lean'
assert module.startswith('NBY_') and p.is_file();assert not (E/a/'receipt.json').exists()
h.admit(a+'UPLOAD')
r=h.remote_py(f'from pathlib import Path\nPath({(h.B+"/NBY_sources/"+module+".lean")!r}).write_text({p.read_text()!r})');assert r.returncode==0,r.stderr
imports=[l.split()[1] for l in p.read_text().splitlines() if l.startswith('import ')]
r=h.remote_py(f'''from pathlib import Path
import hashlib,json
roots=[Path({h.CACHE!r}),Path({h.C!r}),Path({(h.C+'/objects')!r})]
out={{}}
for m in {imports!r}:
 p=next((r/(m.replace('.','/')+'.olean') for r in roots if (r/(m.replace('.','/')+'.olean')).is_file()),None)
 assert p is not None,('missing dependency',m)
 out[m]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
print(json.dumps(out))''');assert r.returncode==0,r.stderr
pins=json.loads(r.stdout)
initial=json.loads((E/'NBY_INITIAL_HOST_PINS.json').read_text())
for n,v in initial['aeneas'].items():pins[n]={'path':n,'sha256':v['sha256']}
cfg=dict(attempt=a,kind='lean',sources=[f'NBY_sources/{module}.lean'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o',h.CACHE+'/'+module+'.olean',f'NBY_sources/{module}.lean'],timeout=180,env={'LEAN_PATH':':'.join([h.CACHE,h.C,h.C+'/objects'])},deps_fingerprint={'selected_objects':pins,'cohort':'SInt2 with shared persistent cache; initial full object pins NBY_INITIAL_HOST_PINS.json'},expected_time='focused symbolic proof, no generated arithmetic')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'NBY_host.py'),a]);sys.exit(r.returncode)
