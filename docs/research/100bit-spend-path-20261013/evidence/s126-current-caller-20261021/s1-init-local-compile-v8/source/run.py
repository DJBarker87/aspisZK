#!/usr/bin/env python3
"""One small LOCAL compile-only diagnostic. Never runs verification or SSH."""
from pathlib import Path
import hashlib,json,os,subprocess,time,signal,re,argparse
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';parser=argparse.ArgumentParser();parser.add_argument('--attempt',default='s1-init-local-compile-v3');parser.add_argument('--harness');args=parser.parse_args();assert re.fullmatch(r's1-init-local-compile-v[0-9]+',args.attempt);A=E/args.attempt;A.mkdir(exist_ok=False)
W=Path('/private/tmp/s126-kani-local-diagnostic-20261025-v1');K=W/'kani-0.67.0';N=Path('/Users/dominic/.rustup/toolchains/nightly-2025-11-21-aarch64-apple-darwin');C=W/'min';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert (K/'rustc-version').read_text().strip()=='rustc 1.93.0-nightly (53732d5e0 2025-11-20)'
# Single local compiler slot; never remove an unknown lock.
lock=Path('/tmp/aspis-local-lean.lock.d');lock.mkdir();(lock/'owner.json').write_text(json.dumps(dict(pid=os.getpid(),branch='codex/s126-caller-20261021',target='S1 local compile-only Kani diagnostic'))+'\n')
try:
 env=dict(os.environ)
 for key in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','RUSTC_BOOTSTRAP']:env.pop(key,None)
 env.update(PATH=str(K/'bin')+':'+str(N/'bin')+':/Users/dominic/.cargo/bin:/usr/bin:/bin:/usr/sbin:/sbin',RUSTUP_TOOLCHAIN='nightly-2025-11-21-aarch64-apple-darwin',DYLD_LIBRARY_PATH=str(N/'lib'),CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(W/'target'),RUSTFLAGS='-C opt-level=3 -Z mir-opt-level=0 -C overflow-checks=yes',KANI_LOG='kani_compiler::kani_middle::transform::check_uninit::ptr_uninit=debug',RUST_BACKTRACE='full')
 source=json.loads((W/'source-binding.json').read_text());source_files={row['path']:sha(W/row['path']) for row in source['native_source_files']};assert all(source_files[row['path']]==row['sha256'] for row in source['native_source_files'])
 for p in [C/'Cargo.toml',C/'Cargo.lock',W/'core-workspace/Cargo.toml']:source_files[str(p.relative_to(W))]=sha(p)
 if (C/'layout.rs').exists():source_files['min/layout.rs']=sha(C/'layout.rs')
 tools=[p for p in K.rglob('*') if p.is_file() and not str(p).startswith(str(K/'toolchain'))]
 tools += [N/'bin/rustc',N/'bin/cargo']+list((N/'lib').glob('*.dylib'))
 tool_pins={str(p):sha(p) for p in tools}
 metadata=[str(N/'bin/cargo'),'metadata','--manifest-path',str(C/'Cargo.toml'),'--offline','--locked','--format-version','1']
 q=subprocess.run(metadata,cwd=C,env=env,text=True,capture_output=True,timeout=20)
 (A/'metadata.stdout.json').write_text(q.stdout);(A/'metadata.stderr.log').write_text(q.stderr)
 if q.returncode!=0:
  (A/'preflight.json').write_text(json.dumps(dict(status='metadata_failed',exit_status=q.returncode,command=metadata,compiler_launched=False,verification_launched=False))+'\n');print(q.stderr[:2000]);raise SystemExit(q.returncode)
 md=json.loads(q.stdout);assert len(md['packages'])==2 and {p['name'] for p in md['packages']}=={'aspis-core','aspis-r1-cost-probe'}
 old=json.loads((E/'s1-claims-row-step-20261024/extra/uninit-min/attempt/receipt.json').read_text())['command']
 cmd=[str(K/'bin/kani-driver'),'kani','--only-codegen','--keep-temps','--verbose',*old[2:]]
 cmd[cmd.index('--manifest-path')+1]=str(C/'Cargo.toml')
 if args.harness:cmd[cmd.index('--harness')+1]=args.harness
 input_record=dict(schema='focused-extractor-proof-packet-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),command=cmd,cwd=str(C),metadata_command=metadata,source_files=source_files,tool_pins=tool_pins,archive=json.loads((W/'release-asset.json').read_text()),source_binding=source,environment={k:env[k] for k in ['PATH','RUSTUP_TOOLCHAIN','DYLD_LIBRARY_PATH','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','RUSTFLAGS','KANI_LOG','RUST_BACKTRACE']},kind='NEW Apple Silicon LOCAL COMPILER DIAGNOSTIC ONLY, no solver/SBF/Linux-equivalence claim',guard=dict(aggregate_rss_limit_bytes=2*2**30,wall_limit_seconds=180,process_limit=64,one_job=True,local_shared_lock=True),expected_time='Compilation plus optimized bounded fixed-table build script, max domain log19; no proof generation/elimination/SAT.',print_axioms='N/A: compiler diagnostic')
 snap=A/'source';snap.mkdir()
 for rel in ['min/Cargo.toml','min/Cargo.lock','min/layout.rs','core-workspace/Cargo.toml']:
  f=W/rel
  if f.exists():dest=snap/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(f.read_bytes())
 (snap/'run.py').write_bytes(Path(__file__).read_bytes())
 (A/'input.json').write_text(json.dumps(input_record,indent=2)+'\n');start=time.monotonic();peak=0;maxprocs=0;stop=None
 with (A/'stdout.log').open('w') as out,(A/'time.log').open('w') as err:
  child=subprocess.Popen(['/usr/bin/time','-l',*cmd],cwd=C,env=env,stdout=out,stderr=err,start_new_session=True)
  pid=child.pid
  while child.poll() is None:
   ps=subprocess.check_output(['ps','-axo','pid=,pgid=,rss='],text=True)
   entries=[list(map(int,l.split())) for l in ps.splitlines() if len(l.split())==3]
   members=[r for r in entries if r[1]==pid];rss=sum(r[2] for r in members)*1024;peak=max(peak,rss);maxprocs=max(maxprocs,len(members))
   if rss>2*2**30:stop='aggregate RSS watchdog'
   elif len(members)>64:stop='process watchdog'
   elif time.monotonic()-start>180:stop='wall watchdog'
   if stop:
    os.killpg(pid,signal.SIGTERM)
    try:child.wait(timeout=2)
    except subprocess.TimeoutExpired:os.killpg(pid,signal.SIGKILL)
    break
   time.sleep(0.2)
  status=child.wait()
 wall=time.monotonic()-start;timing=(A/'time.log').read_text();stdout=(A/'stdout.log').read_text();source_post={path:sha(W/path)==h for path,h in source_files.items()};tools_post={path:sha(Path(path))==h for path,h in tool_pins.items()}
 def metric(label):
  m=re.search(r'(\d+)\s+'+label,timing);return int(m[1]) if m else None
 record=dict(schema='focused-extractor-proof-packet-v1',command=cmd,exit_status=status,wall_seconds=wall,peak_rss_bytes=metric('maximum resident set size'),aggregate_rss_peak_observed_bytes=peak,maximum_processes_observed=maxprocs,swaps=metric('swaps'),watchdog_stop=stop,source_unchanged=source_post,tools_unchanged=tools_post,verification_launched=False,host_SSH_operations=0,print_axioms='N/A: compiler diagnostic',input_sha256=sha(A/'input.json'),stdout_sha256=sha(A/'stdout.log'),stderr_time_sha256=sha(A/'time.log'))
 (A/'receipt.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:record[k] for k in ['exit_status','wall_seconds','peak_rss_bytes','aggregate_rss_peak_observed_bytes','swaps','watchdog_stop','verification_launched']}));print((stdout+'\n'+timing)[-6000:])
 assert all(source_post.values()) and all(tools_post.values())
finally:
 (lock/'owner.json').unlink();lock.rmdir()
