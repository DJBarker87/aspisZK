#!/usr/bin/env python3
"""One capped Aeneas feasibility run on the explicitly pinned guard-only LLBC."""
from __future__ import annotations
import contextlib, fcntl, hashlib, io, json, os, re, runpy, subprocess, sys, time
from pathlib import Path

BASE = Path('/home/dombarker/project-offloads/d18-aeneas-reborrow-v1-20261022')
TOOL = BASE / 'aeneas-trait-guard-v3'
BINARY = TOOL / '_build/default/main.exe'
INPUT = Path('/home/dombarker/project-offloads/s4-fromfn-guard-only-aeneas-v1-20261022/input/from_fn.llbc')
OUT = Path('/home/dombarker/project-offloads/s4-fromfn-guard-only-aeneas-v1-20261022/run-aeneas-v1')
COLLECTOR = Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py')
LOCK = Path('/tmp/aspis-global-extraction-admission-20261019.lock')
COLLECTOR_SHA = '4fc152ea4f88742fb460c301ae17446f1d1ba9162acdaafb37d80e60c4907800'
INPUT_SHA = '97ca029a1fe528f3dfe7c724e9a5793cf0a74c243917193e8db554cbf4af7772'
BINARY_SHA = '8b068c351f82a3a175d9907eece9228872d1165d82ff9380873afccfc10808d9'
IMAGE = 'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
HIGH, MAX, G = 1024**3, 2*1024**3, 1024**3


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def run(cmd, **kw):
    return subprocess.run(cmd, check=True, text=True, capture_output=True, **kw)


def main() -> int:
    assert INPUT.is_file() and sha(INPUT) == INPUT_SHA
    assert BINARY.is_file() and sha(BINARY) == BINARY_SHA
    assert sha(COLLECTOR) == COLLECTOR_SHA
    assert not OUT.exists(), f'refuse overwrite {OUT}'
    OUT.mkdir(parents=True)
    name = re.sub(r'[^A-Za-z0-9_.-]', '-', f's4-fromfn-guard-aeneas-{os.getpid()}-{time.time_ns()}')
    cg_name = None
    with LOCK.open('a') as lf:
        fcntl.flock(lf, fcntl.LOCK_EX)
        capture = io.StringIO()
        with contextlib.redirect_stdout(capture):
            runpy.run_path(str(COLLECTOR))
        inventory = json.loads(capture.getvalue())
        finite = inventory['effective_sum_bytes']
        checks = {
            'finite_plus_new_max_le_48GiB': finite + MAX <= 48*G,
            'MemAvailable_at_least_14GiB': inventory['MemAvailable_kB']*1024 >= 14*G,
        }
        admission = {
            'inventory': inventory, 'checks': checks,
            'requested_caps': {'memory.high': str(HIGH), 'memory.max': str(MAX), 'memory.swap.max': '0'},
            'input_sha256': sha(INPUT), 'compiled_aeneas_binary_sha256': sha(BINARY),
            'candidate_aeneas_source_hash_pin': 'strict-v3 source SHA256 0d2ab7873780feaea346facc38f5429144153f6e93a08aef636509505216bb18; InterpStatements SHA256 1f1b6527bce296728cce288648e6b5f6aa4fd0f1387a06af33fee2642244b616',
            'collector_sha256': COLLECTOR_SHA,
            'docker_image': IMAGE,
            'run_name': name,
        }
        (OUT/'admission-initial.json').write_text(json.dumps(admission,indent=2)+'\n')
        if not all(checks.values()):
            print(json.dumps({'admission':'DENIED','checks':checks}), flush=True)
            return 75
        command = [
            'docker','run','-d','--name',name,
            '--memory='+str(MAX),'--memory-swap='+str(MAX),'--cpus=2','--pids-limit=128','--user','1000:1000',
            '--mount',f'type=bind,src={TOOL},dst=/work,readonly',
            '--mount',f'type=bind,src={INPUT.parent},dst=/input,readonly',
            '--mount',f'type=bind,src={OUT},dst=/output',
            '--workdir','/work','--entrypoint','/bin/sh',IMAGE,
            '-c','while [ ! -f /output/START_AENEAS ]; do sleep 0.1; done; exec opam exec -- /usr/bin/time -v -o /output/time.log /work/_build/default/main.exe -sequential -no-progress-bar -abort-on-error -backend lean -namespace AspisFromFnGuardOnly -dest /output/generated -subdir AspisFromFnGuardOnly -split-files -emit-json /input/from_fn.llbc'
        ]
        (OUT/'command.json').write_text(json.dumps(command,indent=2)+'\n')
        run(command)
        inspect = json.loads(run(['docker','inspect',name]).stdout)[0]
        cid, host_pid = inspect['Id'], inspect['State']['Pid']
        assert len(cid)==64 and host_pid>0
        proc_cgroup = Path(f'/proc/{host_pid}/cgroup').read_text()
        cg_rel = next((line.split('::',1)[1].strip() for line in proc_cgroup.splitlines() if '::' in line), None)
        expected_rel = f'/system.slice/docker-{cid}.scope'
        if cg_rel != expected_rel:
            run(['docker','kill',name])
            raise RuntimeError(f'container cgroup mismatch: {cg_rel!r} != {expected_rel!r}; gated job not released')
        unit = f'docker-{cid}.scope'
        run(['sudo','-n','systemctl','set-property','--runtime',unit,
             f'MemoryHigh={HIGH}',f'MemoryMax={MAX}','MemorySwapMax=0'])
        cg = Path('/sys/fs/cgroup')/cg_rel.lstrip('/')
        keys=('memory.high','memory.max','memory.swap.max')
        limits={k:(cg/k).read_text().strip() for k in keys}
        expected={'memory.high':str(HIGH),'memory.max':str(MAX),'memory.swap.max':'0'}
        if limits != expected:
            run(['docker','kill',name])
            raise RuntimeError(f'actual container cgroup limits mismatch: {limits}')
        admission.update({'container_id':cid,'host_pid':host_pid,'proc_cgroup':proc_cgroup,
                          'cgroup':cg_rel,'systemd_unit':unit,'verified_limits':limits,
                          'gate_released_after_all_limit_checks':True})
        (OUT/'admission-registered.json').write_text(json.dumps(admission,indent=2)+'\n')
        (OUT/'START_AENEAS').touch()
        fcntl.flock(lf, fcntl.LOCK_UN)
    start=time.monotonic()
    status=run(['docker','wait',name], timeout=600).stdout.strip()
    code=int(status)
    # Container remains stopped (no --rm), so collect its exact cgroup counters before removal.
    final={}
    for key in ('memory.current','memory.peak','memory.events','memory.swap.current'):
        p=cg/key
        if p.exists(): final[key]=p.read_text()
    logs=subprocess.run(['docker','logs',name],text=True,capture_output=True)
    (OUT/'stdout.log').write_text(logs.stdout+'\n[stderr]\n'+logs.stderr)
    timing=(OUT/'time.log').read_text() if (OUT/'time.log').exists() else ''
    m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing)
    receipt={'exit_status':code,'wall_seconds':time.monotonic()-start,
             'max_rss_kib':int(m.group(1)) if m else None,'input_sha256':INPUT_SHA,
             'candidate_binary_sha256':BINARY_SHA,'caps':limits,'container_id':cid,
             'host_pid_at_start':host_pid,'proc_cgroup_at_start':proc_cgroup,
             'cgroup_final':final,'docker_exit_status':code,'timed_out':False,
             'generated_files':[]}
    for p in OUT.rglob('*'):
        if p.is_file() and p.name not in {'receipt.json','admission-initial.json','admission-registered.json'}:
            receipt['generated_files'].append(str(p.relative_to(OUT)))
    (OUT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    run(['docker','rm',name])
    return code

if __name__=='__main__':
    raise SystemExit(main())
