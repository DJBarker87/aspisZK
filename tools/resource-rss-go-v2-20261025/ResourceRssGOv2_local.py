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
import ResourceRssGOv2_host as host

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=ROOT/'evidence/resource-rss-go-v2-20261025'
REMOTE=host.STAGE
SSH=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90']
from ResourceRssGOv2_sources import bundle
def coordination():
    # Manager explicitly resolved coordination; no live worker/log inspection.
    return dict(resolved_by='current ResourceRssGOv2 allocation', no_other_authorized_host_worker=True)

def charge():
    coordination()
    with (OUT/'ATTEMPTED').open('x') as f:f.write(host.EPOCH+'; new epoch1/1; prior three failures retained; charged before first SSH including transport failure\n')



def save(name,value):
    with (OUT/name).open('x') as f:json.dump(value,f,indent=2,sort_keys=True);f.write('\n')


def revision():
    return subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()


def sources():
    files={p.name:p.read_text() for p in sorted(HERE.glob('ResourceRssGOv2_*.py'))}
    files['ResourceRssGOv2_reviewed.json']=json.dumps(bundle(),sort_keys=True,indent=2)+chr(10)
    return files


def env(uid):
    return dict(HOME='/home/dombarker',USER='dombarker',LOGNAME='dombarker',PATH='/usr/bin:/bin',LANG='C.UTF-8',
                XDG_RUNTIME_DIR=f'/run/user/{uid}',DBUS_SESSION_BUS_ADDRESS=f'unix:path=/run/user/{uid}/bus')


def ssh_python(payload, label, environment=None, data=None):
    coordination()
    command=SSH+[shlex.join((['/usr/bin/env','-i']+[k+'='+v for k,v in sorted(environment.items())] if environment else [])+
                           ['/usr/bin/python3','-I','-B','-c',payload])]
    start=time.monotonic()
    try:
        result=subprocess.run(command,input=data,text=True,capture_output=True,timeout=120)
    except (OSError,subprocess.SubprocessError) as exc:
        save(label+'-transport.json',dict(command=command,stdin_pin=host.digest((data or '').encode()),exit=None,error=str(exc),wall_seconds=time.monotonic()-start,source_revision=revision(),peak_rss_bytes='N/A unmeasured SSH transport',swap='N/A unmeasured SSH transport',print_axioms='N/A',stdout_base64=base64.b64encode((getattr(exc,'stdout',None) or b'') if isinstance(getattr(exc,'stdout',None),bytes) else (getattr(exc,'stdout',None) or '').encode()).decode(),stderr_base64=base64.b64encode((getattr(exc,'stderr',None) or b'') if isinstance(getattr(exc,'stderr',None),bytes) else (getattr(exc,'stderr',None) or '').encode()).decode()))
        raise
    save(label+'-transport.json',dict(command=command,stdin_pin=host.digest((data or '').encode()),
        exit=result.returncode,wall_seconds=time.monotonic()-start,stdout=result.stdout,stderr=result.stderr,
        source_revision=revision(),peak_rss_bytes='N/A unmeasured SSH transport',swap='N/A unmeasured SSH transport',print_axioms='N/A'))
    return result


def tests():
    label=sys.argv[2] if len(sys.argv)>2 else 'tests'
    if not label.replace('-','').isalnum():raise ValueError('invalid receipt label')
    command=[sys.executable,'-B',str(HERE/'ResourceRssGOv2_tests.py')]
    start=time.monotonic()
    with (OUT/(label+'.log')).open('x') as f:
        child=subprocess.Popen(command,stdout=f,stderr=subprocess.STDOUT)
        _,status,usage=os.wait4(child.pid,0)
        code=os.waitstatus_to_exitcode(status);child.returncode=code
    save(label+'-receipt.json',dict(command=command,exit=code,wall_seconds=time.monotonic()-start,
        peak_rss_bytes=usage.ru_maxrss if platform.system()=='Darwin' else usage.ru_maxrss*1024,swap=usage.ru_nswap,
        source_revision=revision(),interpreter=dict(path=sys.executable,version=sys.version,**host.filepin(Path(sys.executable).resolve())),sources={str(p.relative_to(ROOT)):host.filepin(p) for p in sorted(HERE.glob('*.py'))},
        reviewed_operational={name:{k:v[k] for k in ('revision','path','sha256','size')} for name,v in bundle().items()},
        log_pin=host.filepin(OUT/(label+'.log')),print_axioms='N/A',mode='offline synthetic only'))
    return code


def inspection_payload():
    # No stage creation or scope. Exact runner source is hashed in transport argv.
    # Inspect only the exact runtime pin function from immutable reviewed runner;
    # no main/import of old runner and no stage is created.
    import ast
    tree=ast.parse((HERE/'ResourceRssGOv2_host.py').read_text())
    selected=[n for n in tree.body if isinstance(n,(ast.Import,ast.ImportFrom)) and
              not (isinstance(n,ast.ImportFrom) and (n.module or '').startswith('ResourceRssGOv2')) and
              not any(a.name.startswith('ResourceRssGOv2') for a in n.names)]
    selected += [n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ('digest','filepin','runtime_pins')]
    payload=ast.unparse(ast.Module(body=selected,type_ignores=[]))
    payload += '\n' + (HERE/'ResourceRssGOv2_guard.py').read_text().split('class Proc:')[0]
    bootstrap=payload+"\nif sys.platform != 'linux' or type(resource.RLIM_INFINITY) is not int or resource.RLIM_INFINITY != -1: raise GuardError('unsupported remote Linux resource platform')\nlimits=inherited_limits(); check_limits(limits)\np=Path("+repr(REMOTE)+"); parent=p.parent; assert parent.resolve()==parent; print(json.dumps(dict(runtime=runtime_pins(),inherited_limits=limits,limit_platform=dict(platform=sys.platform,rlim_infinity=resource.RLIM_INFINITY),uid=os.getuid(),stage_exists=p.exists(),parent_uid=parent.stat().st_uid,parent_mode=oct(parent.stat().st_mode & 0o777),parent_resolved=str(parent.resolve()),lock_exists=Path('/tmp/aspis-r0-lean.lock').exists())))"
    return bootstrap


def check_remote_linux_limits(info, expected=None):
    # Fixed Linux Python wire contract, independent of this LOCAL platform.
    metadata=info.get('limit_platform')
    if (type(metadata) is not dict or set(metadata) != {'platform','rlim_infinity'} or
        metadata['platform'] != 'linux' or type(metadata['rlim_infinity']) is not int or
        metadata['rlim_infinity'] != -1):
        raise host.GuardError('unsupported remote Linux resource platform')
    limits=info.get('inherited_limits')
    for candidate in ([limits] if expected is None else [limits,expected]):
        if type(candidate) is not dict or any(
            type(name) is not str or not name.startswith('RLIMIT_') or
            type(pair) is not list or len(pair) != 2 or any(
                type(value) is not int or value < -1 for value in pair)
            for name,pair in candidate.items()):
            raise host.GuardError('malformed remote Linux resource limits')
        for name in ('RLIMIT_AS','RLIMIT_DATA'):
            if candidate.get(name) != [-1,-1]:
                raise host.GuardError('unexpected inherited restriction: '+name)
    if expected is not None and limits != expected:
        raise host.GuardError('inherited resource limits changed; no bypass')


def inspect():
    charge()
    bootstrap=inspection_payload()
    r=ssh_python(bootstrap,'inspect')
    if r.returncode:raise RuntimeError('metadata inspection failed')
    info=json.loads(r.stdout)
    if info['stage_exists'] or info['uid']!=info['parent_uid']:
        raise ValueError('stage exists/conflicting ownership; no writes authorized')
    save('runtime-inspection.json',info)
    check_remote_linux_limits(info)


def stage():
    info=json.loads((OUT/'runtime-inspection.json').read_text())
    check_remote_linux_limits(info)
    files=sources()
    manifest=dict(inherited_limits=info['inherited_limits'],files={name:host.digest(s.encode()) for name,s in files.items()},runtime=info['runtime'],env=env(info['uid']),
                  epoch=host.EPOCH,stage=REMOTE,source_revision=revision(),parent_resolved=info['parent_resolved'],reviewed_base='fbe04424e7553d9b0844ae19c2206b15cf3dd831',mode=host.MODE)
    manifest['scope_argv']=host.scope_argv(manifest)
    save('manifest.json',manifest)
    package=json.dumps(dict(files=files,manifest=manifest))
    bootstrap="""import json,os,pathlib,sys,hashlib
x=json.load(sys.stdin); root=pathlib.Path(REMOTE)
assert not root.exists(), 'existing stage: conflicting writer or prior attempt'
assert root.parent.resolve()==root.parent
assert root.parent.stat().st_uid==os.getuid()
assert str(root.parent.resolve())==x['manifest']['parent_resolved']
root.mkdir(mode=0o700)
for name,source in x['files'].items():
 p=root/name; p.parent.mkdir(mode=0o700,parents=True,exist_ok=True)
 with p.open('x') as f:f.write(source)
 p.chmod(0o444)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==x['manifest']['files'][name]['sha256']
with (root/'ResourceRssGOv2_manifest.json').open('x') as f:json.dump(x['manifest'],f,sort_keys=True,indent=2); f.write(chr(10))
(root/'ResourceRssGOv2_manifest.json').chmod(0o444)
assert json.loads((root/'ResourceRssGOv2_manifest.json').read_text())==x['manifest']
assert root.resolve()==root and root.stat().st_uid==os.getuid() and (root.stat().st_mode & 0o777)==0o700
print(json.dumps(dict(stage=str(root),uid=os.getuid(),files=x['manifest']['files'])))
""".replace('REMOTE',repr(REMOTE))
    r=ssh_python(bootstrap,'stage',environment=manifest['env'],data=package)
    if r.returncode:raise RuntimeError('staging failed; retain stage and stop')


def run():
    coordination()
    # Exclusive local sentinel protects the one live attempt, including transport failures.
    assert (OUT/'ATTEMPTED').exists(), 'epoch not charged before host preparation'
    (OUT/'RUN_ATTEMPTED').open('x').close()
    manifest=json.loads((OUT/'manifest.json').read_text())
    command=SSH+[shlex.join(['/usr/bin/env','-i']+[k+'='+v for k,v in sorted(manifest['env'].items())]+
                           ['/usr/bin/python3','-I','-B',REMOTE+'/ResourceRssGOv2_host.py','run'])]
    start=time.monotonic()
    try:
        r=subprocess.run(command,text=True,capture_output=True,timeout=120)
    except (OSError,subprocess.SubprocessError) as exc:
        save('run-transport.json',dict(command=command,exit=None,error=str(exc),wall_seconds=time.monotonic()-start,source_revision=revision(),manifest_pin=host.filepin(OUT/'manifest.json'),peak_rss_bytes='N/A unmeasured SSH transport',swap='N/A unmeasured SSH transport',print_axioms='N/A',stdout_base64=base64.b64encode((getattr(exc,'stdout',None) or b'') if isinstance(getattr(exc,'stdout',None),bytes) else (getattr(exc,'stdout',None) or '').encode()).decode(),stderr_base64=base64.b64encode((getattr(exc,'stderr',None) or b'') if isinstance(getattr(exc,'stderr',None),bytes) else (getattr(exc,'stderr',None) or '').encode()).decode()))
        raise
    save('run-transport.json',dict(command=command,exit=r.returncode,wall_seconds=time.monotonic()-start,
        stdout=r.stdout,stderr=r.stderr,source_revision=revision(),manifest_pin=host.filepin(OUT/'manifest.json'),
        env_pin=host.digest(json.dumps(manifest['env'],sort_keys=True).encode()),mode_pin=host.digest(host.MODE.encode()),peak_rss_bytes='N/A unmeasured SSH transport',swap='N/A unmeasured SSH transport',print_axioms='N/A'))
    return r.returncode


def preflight():
    manifest=json.loads((OUT/'manifest.json').read_text())
    payload="import sys,json;sys.path.insert(0,"+repr(REMOTE)+");import ResourceRssGOv2_host as h;m=json.loads((h.HERE/'ResourceRssGOv2_manifest.json').read_text());print(json.dumps(h.verify(m),sort_keys=True))"
    result=ssh_python(payload,'stage-preflight',environment=manifest['env'])
    if result.returncode:raise RuntimeError('preflight failure terminal; no retry')

def export():
    coordination()
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
        stderr=r.stderr,host_files=index,full_raw_host=REMOTE+'/capture',peak_rss_bytes='N/A unmeasured SSH transport',swap='N/A unmeasured SSH transport',print_axioms='N/A'))
    return r.returncode

if __name__=='__main__':
    action=sys.argv[1]
    if action not in ('tests','inspect','stage','preflight','run','export'):raise ValueError('unknown action')
    raise SystemExit(globals()[action]() or 0)
