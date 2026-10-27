#!/usr/bin/env python3
"""Receipt collector inside one existing-style capped task scope."""
import datetime,hashlib,json,os,pathlib,re,subprocess,sys,time
job=pathlib.Path('/home/dombarker/project-offloads/codex-pv-srcid-20261026')
name=sys.argv[1];command=sys.argv[2:];out=job/name
now=datetime.datetime.now(datetime.timezone.utc)
assert not (datetime.datetime(2026,10,26,17,45,tzinfo=datetime.timezone.utc) <= now < datetime.datetime(2026,10,26,18,15,tzinfo=datetime.timezone.utc)), 'fixed user quiet window'
out.mkdir(exist_ok=False)
cg=pathlib.Path('/sys/fs/cgroup'+pathlib.Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],map(str,[6*2**30,8*2**30,0,64]))),limits
pins={}
for base in ['crates/aspis-core','crates/aspis-statement','tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters','docs/research/v8-r0-zk-20261009/refine/poseidon']:
 for p in (job/'repo'/base).rglob('*'):
  if p.is_file() and p.suffix in ['.rs','.toml','.lock']:pins[str(p.relative_to(job/'repo'))]=hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic()
with (out/'stdout.log').open('w') as so,(out/'stderr.log').open('w') as se:
 result=subprocess.run(['/usr/bin/time','-v','-o',str(out/'time.log'),*command],cwd=job/'repo',stdout=so,stderr=se)
log=(out/'time.log').read_text()
def metric(key):
 match=re.search(re.escape(key)+r':\s*(\d+)',log);return int(match[1]) if match else None
receipt=dict(name=name,target=command,source_revision=(job/'srcid3-revision.txt').read_text().strip(),source_sha256=pins,deps_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),exit_status=result.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()),cgroup_swap_peak_bytes=int((cg/'memory.swap.peak').read_text()),limits=limits,print_axioms='N/A: Rust/Kani command',expected_time=os.environ['PV_SRCID3_EXPECTED'],environment={k:os.getenv(k) for k in ['RUSTFLAGS','CARGO_TARGET_DIR','CARGO_BUILD_JOBS']},utc=now.isoformat())
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['name','exit_status','wall_seconds','peak_rss_kib','cgroup_memory_peak_bytes','swaps']}),flush=True)
sys.exit(result.returncode)
