"""Local receipt, metadata pin/staging, one-shot transport, and export.

`tests` is offline. `inspect`, `stage`, and `run` are explicit host operations.
No command bootstraps dependencies or accesses worker caches.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import subprocess
import sys
import time
import ResourceActual_host as host

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=ROOT/'evidence/resource-actual-20261024'
REMOTE='/home/dombarker/project-offloads/codex-cx-resource-actual-20261024'
SSH=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90']
REVIEWED=ROOT/'tools/resource-stat-20261024'
OPERATIONAL=['ResourceStat_go.py','ResourceStat_candidate.py','baseline/reservation.py','baseline/reservation_base.py']


def save(name,value):
    with (OUT/name).open('x') as f:json.dump(value,f,indent=2,sort_keys=True);f.write('\n')


def revision():
    return subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()


def sources():
    return {name:(REVIEWED/name).read_text() for name in OPERATIONAL}|{'ResourceActual_host.py':(HERE/'ResourceActual_host.py').read_text()}


def env(uid):
    return dict(HOME='/home/dombarker',USER='dombarker',LOGNAME='dombarker',PATH='/usr/bin:/bin',LANG='C.UTF-8',
                XDG_RUNTIME_DIR=f'/run/user/{uid}',DBUS_SESSION_BUS_ADDRESS=f'unix:path=/run/user/{uid}/bus')


def ssh_python(payload, label, environment=None, data=None):
    command=SSH+[shlex.join((['env','-i']+[k+'='+v for k,v in sorted(environment.items())] if environment else [])+
                           ['/usr/bin/python3','-I','-B','-c',payload])]
    start=time.monotonic()
    result=subprocess.run(command,input=data,text=True,capture_output=True,timeout=120)
    save(label+'-transport.json',dict(command=command,stdin_pin=host.digest((data or '').encode()),
        exit=result.returncode,wall_seconds=time.monotonic()-start,stdout=result.stdout,stderr=result.stderr,
        source_revision=revision(),print_axioms='N/A'))
    return result


def tests():
    command=[sys.executable,'-B',str(HERE/'ResourceActual_tests.py')]
    start=time.monotonic()
    with (OUT/'tests.log').open('x') as f:
        child=subprocess.Popen(command,stdout=f,stderr=subprocess.STDOUT)
        _,status,usage=os.wait4(child.pid,0)
        code=os.waitstatus_to_exitcode(status);child.returncode=code
    save('tests-receipt.json',dict(command=command,exit=code,wall_seconds=time.monotonic()-start,
        peak_rss_bytes=usage.ru_maxrss if platform.system()=='Darwin' else usage.ru_maxrss*1024,swap=usage.ru_nswap,
        source_revision=revision(),sources={str(p.relative_to(ROOT)):host.filepin(p) for p in sorted(HERE.glob('*.py'))},
        reviewed_operational={name:host.filepin(REVIEWED/name) for name in OPERATIONAL},
        log_pin=host.filepin(OUT/'tests.log'),print_axioms='N/A',mode='offline synthetic only'))
    return code


def inspect():
    # No stage creation or scope. Exact runner source is hashed in transport argv.
    payload=(HERE/'ResourceActual_host.py').read_text()+"\n"
    # __main__ would dispatch: execute source with a non-main namespace instead.
    bootstrap="import json,os,pathlib; ns={'__file__':"+repr(REMOTE+'/ResourceActual_host.py')+",'__name__':'pin_inspect'}; exec("+repr(payload)+",ns); p=pathlib.Path("+repr(REMOTE)+"); parent=p.parent; print(json.dumps(dict(runtime=ns['runtime_pins'](),uid=os.getuid(),stage_exists=p.exists(),parent_uid=parent.stat().st_uid,parent_mode=oct(parent.stat().st_mode & 0o777),lock_exists=pathlib.Path('/tmp/aspis-r0-lean.lock').exists())))"
    r=ssh_python(bootstrap,'inspect')
    if r.returncode:raise RuntimeError('metadata inspection failed')
    info=json.loads(r.stdout)
    if info['stage_exists'] or info['uid']!=info['parent_uid']:
        raise ValueError('stage exists/conflicting ownership; no writes authorized')
    save('runtime-inspection.json',info)


def stage():
    info=json.loads((OUT/'runtime-inspection.json').read_text())
    files=sources()
    manifest=dict(files={name:host.digest(s.encode()) for name,s in files.items()},runtime=info['runtime'],env=env(info['uid']),
                  source_revision=revision(),reviewed_base='74d67bcc99a749152ee0a400876b0e2169531bfd',mode=host.MODE)
    save('manifest.json',manifest)
    package=json.dumps(dict(files=files,manifest=manifest))
    bootstrap="""import json,os,pathlib,sys,hashlib
x=json.load(sys.stdin); root=pathlib.Path(REMOTE)
assert not root.exists(), 'existing stage: conflicting writer or prior attempt'
assert root.parent.stat().st_uid==os.getuid()
root.mkdir(mode=0o700)
for name,source in x['files'].items():
 p=root/name; p.parent.mkdir(mode=0o700,parents=True,exist_ok=True)
 with p.open('x') as f:f.write(source)
 p.chmod(0o444)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==x['manifest']['files'][name]['sha256']
with (root/'manifest.json').open('x') as f:json.dump(x['manifest'],f,sort_keys=True,indent=2); f.write(chr(10))
(root/'manifest.json').chmod(0o444)
print(json.dumps(dict(stage=str(root),uid=os.getuid(),files=x['manifest']['files'])))
""".replace('REMOTE',repr(REMOTE))
    r=ssh_python(bootstrap,'stage',environment=manifest['env'],data=package)
    if r.returncode:raise RuntimeError('staging failed; retain stage and stop')


def run():
    # Exclusive local sentinel protects the one live attempt, including transport failures.
    (OUT/'ATTEMPTED').open('x').close()
    manifest=json.loads((OUT/'manifest.json').read_text())
    command=SSH+[shlex.join(['env','-i']+[k+'='+v for k,v in sorted(manifest['env'].items())]+
                           ['/usr/bin/python3','-I','-B',REMOTE+'/ResourceActual_host.py','run'])]
    start=time.monotonic()
    r=subprocess.run(command,text=True,capture_output=True,timeout=120)
    save('run-transport.json',dict(command=command,exit=r.returncode,wall_seconds=time.monotonic()-start,
        stdout=r.stdout,stderr=r.stderr,source_revision=revision(),manifest_pin=host.filepin(OUT/'manifest.json'),
        env_pin=host.digest(json.dumps(manifest['env'],sort_keys=True).encode()),mode_pin=host.digest(host.MODE.encode()),print_axioms='N/A'))
    return r.returncode


def export():
    # Read only own stage. Full raw originals stay remote; bounded meaningful shards locally.
    payload="""import base64,json,pathlib,hashlib
root=pathlib.Path(REMOTE)/'capture'
for p in sorted(root.iterdir()):
 b=p.read_bytes(); print(json.dumps(dict(name=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),data=base64.b64encode(b).decode())))
""".replace('REMOTE',repr(REMOTE))
    command=SSH+[shlex.join(['/usr/bin/python3','-I','-B','-c',payload])]
    start=time.monotonic();r=subprocess.run(command,capture_output=True,text=True,timeout=60)
    index={}
    for line in r.stdout.splitlines():
        obj=json.loads(line);raw=base64.b64decode(obj.pop('data'))
        assert host.digest(raw)==dict(sha256=obj['sha256'],size=obj['size'])
        name=obj['name'];assert Path(name).name==name
        index[name]=obj
        if len(raw)<=5_000_000:
            with (OUT/name).open('xb') as f:f.write(raw)
        else:
            save(name+'.hash.json',obj)
            value=json.loads(raw)
            if name.endswith('-ordered.json'):
                # About 0.5-1MB/shard; retain all ordered events without tiny files.
                for i in range(0,len(value),1000):
                    save(name[:-5]+f'-{i//1000:03d}.json',value[i:i+1000])
            elif name.endswith('-report.json'):
                # Report has repeated raw input, also retained in ordered capture.
                for snapshot in value.get('snapshots',{}).values():
                    if snapshot:
                        for key in ('raw_inputs','read_attempts','self_read_attempts'):snapshot.pop(key,None)
                save(name[:-5]+'-summary.json',value)
    save('export-receipt.json',dict(command=command,exit=r.returncode,wall_seconds=time.monotonic()-start,
        stderr=r.stderr,host_files=index,full_raw_host=REMOTE+'/capture',print_axioms='N/A'))
    return r.returncode

if __name__=='__main__':
    action=sys.argv[1]
    if action not in ('tests','inspect','stage','run','export'):raise ValueError('unknown action')
    raise SystemExit(globals()[action]() or 0)
