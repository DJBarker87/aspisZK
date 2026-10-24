"""One independently capped Docker/systemd scope; never use shared source mounts."""
from pathlib import Path
import datetime, hashlib, json, subprocess, sys, time, runpy

D = Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/native-drop/backend')
IMAGE = 'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
attempt = int(sys.argv[1])
assert 8 <= attempt <= 12
name = f'prover-rw-native-drop-build-{attempt:03d}'
O = D/name
O.mkdir()  # An existing attempt is never overwritten or rerun.
scanner = runpy.run_path(str(Path(__file__).resolve().parents[1]/'native-entropy/reservation.py'))
admission = scanner['admission']()
(O/'reservation-before-create.json').write_text(json.dumps(admission, indent=2)+'\n')
assert admission['allowed'], admission
rows = admission['cgroups']
command = ['docker', 'create', '--name', name, '--network', 'none', '--memory', '8g',
    '--memory-swap', '8g', '--pids-limit', '64', '--cpus', '4', '--user', '0',
    '--mount', f'type=bind,src={D},dst=/job', '--mount', 'type=bind,src=/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor/deps,dst=/prior-deps,readonly', '--entrypoint', '/bin/bash', IMAGE,
    '-c', 'while [ ! -f /job/'+name+'/go ]; do sleep 0.1; done; exec /usr/bin/time -v -o /job/'+name+'/time.log opam exec -- bash /job/build-base.sh']
preflight = dict(command=command, expected_phase='Optimized OCaml compilation of private candidate008; pinned Charon/deps cache reused read-only; no Rust/extraction/proof generation.',
    source_revision=(D/'revision.txt').read_text().strip(), provenance_sha256=hashlib.sha256((D/'base-provenance.json').read_bytes()).hexdigest(), dependency_manifest_sha256=hashlib.sha256((D/'dependency-manifest.json').read_bytes()).hexdigest(),
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
# Only this owned container may be stopped on failed admission; no other
# service/container is inspected for mutation or killed.
release = runpy.run_path(str(Path(__file__).resolve().parents[1]/'native-entropy/docker_gate.py'))['release']
start = time.monotonic()
try:
    limits = release(cg, O, scanner['admission'])
except BaseException:
    subprocess.run(['docker','stop','--time','1',cid], check=True, stdout=subprocess.DEVNULL)
    raise
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
