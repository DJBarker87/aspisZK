#!/usr/bin/env python3
"""One capped attempt, with immutable command/source/resource receipt."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time,datetime
R=Path(__file__).resolve().parents[2]; H=R/'receipts'; H.mkdir(exist_ok=True)
name=sys.argv[1];cmd=sys.argv[2:];O=H/name;O.mkdir()
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},limits
pins={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for base in ['tools/prover-rw-20261023','tools/ct-kernels-20261022','tools/r1-builder-reference','crates/aspis-core','crates/aspis-r1-cost-probe','crates/aspis-prover','crates/aspis-statement','programs/r1-cost-probe','programs/aspis-pool','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3'] for p in (R/base).rglob('*') if p.is_file() and 'target' not in p.parts and '__pycache__' not in p.parts and p.suffix!='.pyc'}

for q in ['Cargo.toml','Cargo.lock']:
 pins[q]=hashlib.sha256((R/q).read_bytes()).hexdigest()
input_artifacts={}
for arg in cmd:
 p=Path(arg)
 if not p.is_absolute():p=R/p
 if p.suffix=='.llbc' and p.is_file():
  data=p.read_bytes();(O/'inputs').mkdir(exist_ok=True)
  (O/'inputs'/p.name).write_bytes(data)
  input_artifacts[str(p)]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'retained':str(O/'inputs'/p.name)}
  llbc=json.loads(data)['translated'];bindings={}
  for f in llbc['files']:
   local=f['name'].get('Local')
   if not local or f.get('contents') is None:continue
   source=Path(local)
   if not source.is_absolute():source=R/source
   try:relative=str(source.resolve().relative_to(R.resolve()))
   except ValueError:continue
   digest=hashlib.sha256(f['contents'].encode()).hexdigest()
   bindings[relative]=dict(llbc_source_sha256=digest,live_source_sha256=pins.get(relative),matches_live_source=digest==pins.get(relative))
  input_artifacts[str(p)]['source_bindings']=bindings
  input_artifacts[str(p)]['source_map_consistent_with_live_tree']=bool(bindings) and all(v['matches_live_source'] for v in bindings.values())

(O/'preflight.json').write_text(json.dumps(dict(target=cmd,input_artifacts=input_artifacts,source_revision=(R/'source-revision.txt').read_text().strip(),source_sha256=pins,limits=limits,cgroup=str(cg),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),loadavg=Path('/proc/loadavg').read_text().strip(),expected_work=os.getenv('CT_EXPECTED')),indent=2)+'\n')
start=time.monotonic()
with (O/'stdout.log').open('w') as so,(O/'stderr.log').open('w') as se:
 try:
  ret=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],cwd=R,stdout=so,stderr=se).returncode
 except KeyboardInterrupt:
  ret=130
log=(O/'time.log').read_text();metric=lambda n:int(re.search(re.escape(n)+r':\s*(\d+)',log)[1]) if re.search(re.escape(n)+r':\s*(\d+)',log) else None
rec={'schema':'focused-extractor-proof-packet-v1','attempt':name,'target':cmd,'input_artifacts':input_artifacts,'source_revision':(R/'source-revision.txt').read_text().strip(),'source_sha256':pins,'deps_fingerprint':hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),'exit_status':ret,'wall_seconds':time.monotonic()-start,'peak_rss_kib':metric('Maximum resident set size (kbytes)'),'swaps':metric('Swaps'),'print_axioms':'N/A: Rust or translation; no Lean theorem checked','cgroup':str(cg),'cgroup_memory_peak_bytes':int((cg/'memory.peak').read_text()),'cgroup_swap_peak_bytes':int((cg/'memory.swap.peak').read_text()),'cgroup_memory_events':dict(line.split() for line in (cg/'memory.events').read_text().splitlines()),'cgroup_pids_peak':int((cg/'pids.peak').read_text()) if (cg/'pids.peak').exists() else None,'rss_measurement':'GNU time maximum resident set size; timeout descendants may not be reaped and this RSS can undercount; cgroup peak is separate','limits':limits,'environment':{k:os.getenv(k) for k in ['CARGO_PROFILE_DEV_OPT_LEVEL','CARGO_BUILD_JOBS','CARGO_TARGET_DIR','RUSTFLAGS']},'expected_work':os.getenv('CT_EXPECTED','compilation then named harness; no elimination'),'errors_log':'stderr.log','toolchain':subprocess.run(['rustc','-Vv'],capture_output=True,text=True).stdout,'loadavg':Path('/proc/loadavg').read_text().strip(),'cpu':subprocess.run(['lscpu'],capture_output=True,text=True).stdout}
(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({k:rec[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(ret)
