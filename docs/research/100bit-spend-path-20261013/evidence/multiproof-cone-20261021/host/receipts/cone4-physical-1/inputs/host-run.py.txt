#!/usr/bin/env python3
"""One capped attempt, with immutable command/source/resource receipt."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
R=Path(__file__).resolve().parents[2]; H=R/'receipts'; H.mkdir(exist_ok=True)
name=sys.argv[1];cmd=sys.argv[2:];O=H/name;O.mkdir()
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},limits
pins={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for base in ['tools/multiproof-cone-20261021','crates/aspis-core/src','crates/aspis-r1-cost-probe/src'] for p in (R/base).rglob('*') if p.is_file() and 'target' not in p.parts}
# Preserve every proof input before compilation, including failed attempts.
inputs=O/'inputs';inputs.mkdir()
for p in (R/'tools/multiproof-cone-20261021').rglob('*'):
 if p.is_file() and 'target' not in p.parts and p.suffix in ['.rs','.py','.toml','.lock']:
  (inputs/(str(p.relative_to(R/'tools/multiproof-cone-20261021')).replace('/','--')+'.txt')).write_bytes(p.read_bytes())
start=time.monotonic()
with (O/'stdout.log').open('w') as so,(O/'stderr.log').open('w') as se:
 ret=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],cwd=R,stdout=so,stderr=se).returncode
raw_ret=ret
kani_validation=None
if 'kani' in cmd:
 expected=cmd.count('--harness')
 output=(O/'stdout.log').read_text()
 successful=output.count('VERIFICATION SUCCESSFUL')
 failed=output.count('VERIFICATION FAILED')
 kani_validation={'expected_harnesses':expected,'successful_verifier_results':successful,'failed_verifier_results':failed,'complete':successful==expected and expected>0 and failed==0}
 if ret==0 and not kani_validation['complete']:ret=65
log=(O/'time.log').read_text();metric=lambda n:int(re.search(re.escape(n)+r':\s*(\d+)',log)[1]) if re.search(re.escape(n)+r':\s*(\d+)',log) else None
rec={'schema':'focused-extractor-proof-packet-v1','attempt':name,'target':cmd,'source_revision':(R/'source-revision.txt').read_text().strip(),'source_sha256':pins,'deps_fingerprint':hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),'exit_status':ret,'raw_tool_exit_status':raw_ret,'kani_verifier_validation':kani_validation,'optimization_environment':{k:os.getenv(k) for k in ['CARGO_PROFILE_DEV_OPT_LEVEL','CARGO_PROFILE_DEV_DEBUG','RUSTFLAGS']},'wall_seconds':time.monotonic()-start,'peak_rss_kib':metric('Maximum resident set size (kbytes)'),'swaps':metric('Swaps'),'print_axioms':'N/A: Rust or translation; no Lean theorem checked','cgroup':str(cg),'cgroup_memory_peak_bytes':int((cg/'memory.peak').read_text()),'cgroup_swap_peak_bytes':int((cg/'memory.swap.peak').read_text()),'rss_measurement':'GNU time maximum resident set size; timeout descendants may not be reaped and this RSS can undercount; cgroup peak is separate','limits':limits,'expected_work':os.getenv('MP_EXPECTED','compilation then named harness; no elimination'),'errors_log':'stderr.log'}
(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({k:rec[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(ret)
