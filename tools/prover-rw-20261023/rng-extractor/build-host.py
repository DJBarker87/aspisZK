"""One independently capped Docker/systemd scope; never use shared source mounts."""
from pathlib import Path
import datetime, hashlib, json, subprocess, sys, time

D = Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor')
IMAGE = 'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
attempt = int(sys.argv[1])
assert 5 <= attempt <= 8
name = f'prover-rw-rng-extractor-build-{attempt:03d}'
O = D/name
O.mkdir()  # An existing attempt is never overwritten or rerun.
root = Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice')
rows = []
for p in root.glob('*.scope'):
    try:
        if not (p/'cgroup.procs').read_text().split():
            continue
        cap = (p/'memory.max').read_text().strip()
        assert cap != 'max', str(p)
        rows.append(dict(scope=str(p), memory_max=int(cap)))
    except FileNotFoundError:
        continue
assert sum(r['memory_max'] for r in rows)+8*2**30 < 55*2**30
command = ['docker', 'create', '--name', name, '--network', 'none', '--memory', '8g',
    '--memory-swap', '8g', '--pids-limit', '64', '--cpus', '4', '--user', '0',
    '--mount', f'type=bind,src={D},dst=/job', '--entrypoint', '/bin/bash', IMAGE,
    '-c', 'while [ ! -f /job/'+name+'/go ]; do sleep 0.1; done; exec /usr/bin/time -v -o /job/'+name+'/time.log opam exec -- bash /job/build-base.sh']
preflight = dict(command=command, expected_phase='Optimized OCaml compilation of pinned Charon dependency then pinned extended Aeneas base; no Rust arithmetic, extraction or proof generation.',
    source_revision='3747025cbf+continuation005', provenance_sha256=hashlib.sha256((D/'base-provenance.json').read_bytes()).hexdigest(),
    populated_reservations=rows, requested_memory_max=8*2**30, build_attempt=attempt,
    candidate_source_sha256={str(p.relative_to(D/'base')):hashlib.sha256(p.read_bytes()).hexdigest() for p in (D/'base').rglob('*') if p.is_file() and not p.is_symlink() and '_build' not in p.parts and '.git' not in p.parts},
    driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    build_script_sha256=hashlib.sha256((D/'build-base.sh').read_bytes()).hexdigest(),
    utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(O/'preflight.json').write_text(json.dumps(preflight, indent=2)+'\n')
cid = subprocess.check_output(command, text=True).strip()
subprocess.run(['docker', 'start', cid], check=True, stdout=subprocess.DEVNULL)
info = json.loads(subprocess.check_output(['docker', 'inspect', cid]))[0]
pid = info['State']['Pid']
cg = Path('/sys/fs/cgroup'+Path(f'/proc/{pid}/cgroup').read_text().split('0::')[1].strip())
subprocess.run(['sudo', '-n', 'tee', str(cg/'memory.high')], input=str(6*2**30), text=True, check=True, stdout=subprocess.DEVNULL)
limits = {k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits == dict(zip(limits, [str(6*2**30),str(8*2**30),'0','64'])), limits
(O/'cap-receipt.json').write_text(json.dumps(dict(cgroup=str(cg),limits=limits,container_id=cid), indent=2)+'\n')
start = time.monotonic()
(O/'go').touch()
waiter = subprocess.Popen(['docker', 'wait', cid], text=True, stdout=subprocess.PIPE)
peaks = {}
while waiter.poll() is None:
    for key in ['memory.peak','memory.swap.peak','pids.peak']:
        try: peaks[key] = max(peaks.get(key,0), int((cg/key).read_text()))
        except FileNotFoundError: pass
    time.sleep(0.1)
exit_code = int(waiter.communicate()[0].strip())
log = subprocess.check_output(['docker', 'logs', cid], stderr=subprocess.STDOUT)
(O/'output.log').write_bytes(log)
receipt = dict(preflight, exit_status=exit_code, wall_seconds=time.monotonic()-start,
    limits=limits, cgroup=str(cg), observed_cgroup_peaks=peaks, print_axioms='N/A: OCaml backend build; no Lean invocation')
# Docker removes the process cgroup on exit. GNU time records RSS and swap;
# retain container inspect too, including OOMKilled and exact process status.
receipt['container_state'] = json.loads(subprocess.check_output(['docker','inspect',cid]))[0]['State']
if exit_code == 0:
    import shutil
    versioned = D/f'candidate-{attempt:03d}'
    versioned.mkdir()
    binary = D/'base/src/_build/default/main.exe'
    shutil.copy2(binary, versioned/'main.exe')
    receipt['versioned_binary'] = dict(path=str(versioned/'main.exe'),sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),bytes=binary.stat().st_size)
receipt['time_log'] = (O/'time.log').read_text() if (O/'time.log').exists() else None
(O/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(dict(exit_status=exit_code,wall_seconds=receipt['wall_seconds'])))
raise SystemExit(exit_code)
