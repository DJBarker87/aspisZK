"""Own-directory sequential driver; the standing shared launcher is unchanged.
Called with a frozen manifest. Every compile gets its own admission check and
launcher scope; no parallel compilation and no unchanged failed-target retry.
"""
from pathlib import Path
import subprocess,json,re,hashlib,sys,time,datetime
manifest=Path(sys.argv[1]);spec=json.loads(manifest.read_text());out=manifest.parent
base=Path('/home/dombarker/project-offloads');shared=base/'aspis-joint-20261019'
launcher=base/'r1-privacy-build-integration-20261019/tools/run-joint.sh'
scanner=base/'codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
env=json.loads((base/'r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[str(shared/'objects')]+env['LEAN_PATH'].split(':')
for row in spec:
    attempt=row['attempt'];module=row['module'];source=shared/'sources'/(module+'.lean')
    assert hashlib.sha256(source.read_bytes()).hexdigest()==row['source_sha256']
    admission=out/f'{attempt}-admission.json'
    quiet=base/'QUIET_WINDOW.json'
    until=float(json.loads(quiet.read_text()).get('until',0)) if quiet.exists() else 0
    if time.time()<until:
        admission.write_text(json.dumps(dict(allowed=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),reason='QUIET WINDOW HOLD',until=until)))
        sys.exit(78)
    gate=subprocess.run(['python3',str(scanner),str(admission)],capture_output=True,text=True)
    (out/f'{attempt}-admission.log').write_text(gate.stdout+gate.stderr)
    if gate.returncode:
        print(json.dumps(dict(attempt=attempt,refused=True)),flush=True);sys.exit(78)
    imports=re.findall(r'^import (\S+)',source.read_text(),re.M);ids={}
    for imp in imports:
        for directory in paths:
            p=Path(directory)/(imp.replace('.','/')+'.olean')
            if p.exists():
                ids[imp]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest());break
        else:ids[imp]='MISSING'
    fp=hashlib.sha256(json.dumps(ids,sort_keys=True).encode()).hexdigest()
    (out/f'{attempt}-preflight.json').write_text(json.dumps(dict(module=module,dependency_objects=ids,deps_fingerprint=fp,revision=row['revision']),indent=2)+'\n')
    p=subprocess.run([str(launcher),str(attempt),module,'J','7000','8',fp],capture_output=True,text=True)
    log=p.stdout+p.stderr;(out/f'{attempt}-launch.log').write_text(log)
    print(json.dumps(dict(attempt=attempt,module=module,launcher_exit=p.returncode,compiler_exit=re.findall(r'^exit=(\d+)',log,re.M))),flush=True)
    exits=re.findall(r'^exit=(\d+)',log,re.M)
    code=int(exits[-1]) if exits else (p.returncode or 78)
    if code:sys.exit(code)
