#!/usr/bin/env python3
"""One focused native negative-control verification, atomic local lock."""
from pathlib import Path
import hashlib,json,os,re,signal,subprocess,time
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
A=E/'s6-native-box-wrapper-negative-local-v1';A.mkdir()
W=Path('/private/tmp/s126-native-box-wrapper-20261026-v5')
K=Path('/private/tmp/s126-kani-local-diagnostic-20261025-v1/kani-0.67.0')
N=Path('/Users/dominic/.rustup/toolchains/nightly-2025-11-21-aarch64-apple-darwin')
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
lock=Path('/tmp/aspis-local-lean.lock.d');lock.mkdir()
(lock/'owner.json').write_text(json.dumps({'pid':os.getpid(),'target':'S6 native boxed wrapper negative verification','branch':'codex/s126-caller-20261021'})+'\n')
try:
 env=dict(os.environ)
 for key in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','RUSTC_BOOTSTRAP']:env.pop(key,None)
 env.update(PATH=str(K/'bin')+':'+str(N/'bin')+':/Users/dominic/.cargo/bin:/usr/bin:/bin:/usr/sbin:/sbin',RUSTUP_TOOLCHAIN='nightly-2025-11-21-aarch64-apple-darwin',DYLD_LIBRARY_PATH=str(N/'lib'),CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR='/private/tmp/s126-native-box-wrapper-local-target-v1',RUSTFLAGS='-C opt-level=3 -Z mir-opt-level=0 -C overflow-checks=yes')
 assert (K/'rustc-version').read_text().strip()=='rustc 1.93.0-nightly (53732d5e0 2025-11-20)'
 plan=json.loads((W/'plan.json').read_text());before={p:sha(W/p) for p in plan['files']};assert before==plan['files']
 package_pins=json.loads((W/'registry-pins.json').read_text())
 def imports():
  root=Path('/Users/dominic/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
  return {pkg:{f:sha(root/pkg/f) for f in meta['files']} for pkg,meta in package_pins.items()}
 ip=imports();assert all(ip[pkg]==meta['files'] for pkg,meta in package_pins.items())
 toolpaths=[p for p in (K/'bin').iterdir() if p.is_file()]+[K/'rustc-version',N/'bin/rustc',N/'bin/cargo']
 toolpaths+=[p for p in (K/'lib').glob('*') if p.is_file()]+list((N/'lib').glob('*.dylib'))+[p for p in (N/'lib/rustlib/aarch64-apple-darwin/lib').glob('*') if p.is_file()]
 tp={str(p):sha(p) for p in toolpaths}
 cmd=[str(K/'bin/kani-driver'),'kani','--manifest-path',str(W/'harness/Cargo.toml'),'--lib','--exact','--harness','proofs::last_frontier_negative_control','--solver','cadical','--no-assertion-reach-checks','-j','1','-Z','unstable-options','-Z','stubbing','--output-format','terse','--harness-timeout','120','--keep-temps']
 inp={'schema':'focused-extractor-proof-packet-v1','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'command':cmd,'cwd':str(W/'harness'),'environment':{k:env[k] for k in ['PATH','RUSTUP_TOOLCHAIN','DYLD_LIBRARY_PATH','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','RUSTFLAGS']},'source_pins':before,'import_pins':ip,'tool_pins':tp,'source_binding':json.loads((W/'binding.json').read_text()),'guard':{'aggregate_rss_max_bytes':4*2**30,'wall_limit_seconds':180,'process_limit':64,'atomic_local_lock':True},'verification_launched':True,'expected_time':'Focused negative-control verification on native aarch64/darwin; whole-byte domain and complete native carriers, original decoder Result cut. Existing compiled package cache, one job,4GiB watchdog; no extraction/SBF/Lean build. Distinct target from Linux positive-family certificates; negative assertion must fail.'}
 (A/'input.json').write_text(json.dumps(inp,indent=2)+'\n');(A/'runner.py').write_bytes(Path(__file__).read_bytes())
 start=time.monotonic();peak=0;maximum=0;stop=None
 with (A/'stdout.log').open('w') as out,(A/'time.log').open('w') as err:
  child=subprocess.Popen(['/usr/bin/time','-l',*cmd],cwd=W/'harness',env=env,stdout=out,stderr=err,start_new_session=True)
  while child.poll() is None:
   ps=subprocess.check_output(['ps','-axo','pid=,pgid=,rss='],text=True)
   entries=[list(map(int,l.split())) for l in ps.splitlines() if len(l.split())==3]
   members=[row for row in entries if row[1]==child.pid];rss=sum(row[2] for row in members)*1024
   peak=max(peak,rss);maximum=max(maximum,len(members))
   if rss>4*2**30:stop='aggregate RSS watchdog'
   elif len(members)>64:stop='process watchdog'
   elif time.monotonic()-start>180:stop='wall watchdog'
   if stop:
    os.killpg(child.pid,signal.SIGTERM)
    try:child.wait(timeout=2)
    except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL)
    break
   time.sleep(.2)
  status=child.wait()
 timing=(A/'time.log').read_text()
 def metric(label):
  match=re.search(r'(\d+)\s+'+label,timing);return int(match[1]) if match else None
 rec={'schema':'focused-extractor-proof-packet-v1','command':cmd,'exit_status':status,'wall_seconds':time.monotonic()-start,'peak_rss_bytes':metric('maximum resident set size'),'aggregate_rss_peak_observed_bytes':peak,'maximum_processes_observed':maximum,'swaps':metric('swaps'),'watchdog_stop':stop,'source_unchanged':all(sha(W/p)==h for p,h in before.items()),'imports_unchanged':imports()==ip,'tools_unchanged':all(sha(Path(p))==h for p,h in tp.items()),'verification_launched':True,'print_axioms':'N/A: native Kani negative control','input_sha256':sha(A/'input.json'),'stdout_sha256':sha(A/'stdout.log'),'stderr_time_sha256':sha(A/'time.log')}
 (A/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
 print(json.dumps({k:rec[k] for k in ['exit_status','wall_seconds','peak_rss_bytes','aggregate_rss_peak_observed_bytes','swaps','watchdog_stop']}))
 assert rec['source_unchanged'] and rec['imports_unchanged'] and rec['tools_unchanged']
finally:
 (lock/'owner.json').unlink();lock.rmdir()
