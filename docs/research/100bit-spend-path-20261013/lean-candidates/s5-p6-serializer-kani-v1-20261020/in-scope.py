from pathlib import Path
import json,subprocess,os,sys,time,hashlib,re,signal
w=Path(__file__).resolve().parent;e=Path(sys.argv[1]);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::',1)[1].strip())
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']}
assert limits['memory.swap.max']=='0' and int(limits['memory.max'])==2*2**30
assert sha(w/'src/lib.rs')==json.loads((w/'source-binding.json').read_text())['generated_source_sha256']
kani=Path('/home/dombarker/.cargo/bin/cargo-kani')
tools=[kani]+[Path('/home/dombarker/.kani/kani-0.67.0/bin')/x for x in ['kani-driver','kani-compiler','cbmc','kissat']]
cmd=[str(kani),'--manifest-path',str(w/'Cargo.toml'),'--lib','--exact','--harness','original_serializer_matches_captured_writeback','--solver','kissat','--output-format','regular','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ.get('PATH','/usr/bin:/bin'),CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_TEST_OPT_LEVEL='3',CARGO_TARGET_DIR=str(w/'target'))
pre={'command':cmd,'tool_sha256':{str(t):sha(t) for t in tools},'limits':limits,'source_sha256':sha(w/'src/lib.rs'),'source_binding':json.loads((w/'source-binding.json').read_text()),'cargo_manifest_sha256':sha(w/'Cargo.toml'),'source_revision':(w/'source-revision.txt').read_text().strip(),'expected_time':'Kani MIR compilation then one fixed eight-limb serializer symbolic-equivalence step; no finite-field elimination. Cargo dev/test opt-level=3; default memory/overflow/undefined/unwind/reachability checks enabled.','environment':{k:env[k] for k in ['PATH','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_PROFILE_DEV_OPT_LEVEL','CARGO_PROFILE_TEST_OPT_LEVEL','CARGO_TARGET_DIR']}}
(e/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n');start=time.monotonic();reason=None
with (e/'kani.log').open('w') as f:
 p=subprocess.Popen(['/usr/bin/time','-v','-o',str(e/'time.log')]+cmd,cwd=w,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
 try:code=p.wait(timeout=300)
 except subprocess.TimeoutExpired:
  reason='focused job 300-second review threshold';os.killpg(p.pid,signal.SIGTERM)
  try:code=p.wait(timeout=3)
  except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);code=p.wait()
txt=(e/'time.log').read_text() if (e/'time.log').exists() else '';get=lambda s:int(re.search(re.escape(s)+r':\s*(\d+)',txt)[1]) if re.search(re.escape(s)+r':\s*(\d+)',txt) else None
rec={'exit_status':code,'wall_seconds':round(time.monotonic()-start,3),'peak_rss_kib':get('Maximum resident set size (kbytes)'),'swaps':get('Swaps'),'scope_memory_peak_bytes':int((cg/'memory.peak').read_text()),'scope_swap_peak_bytes':int((cg/'memory.swap.peak').read_text()),'limits':limits,'source_revision':pre['source_revision'],'source_sha256':pre['source_sha256'],'watchdog_abort':reason,'print_axioms':'N/A: Kani symbolic proof; no claim of a Lean-kernel Rust/stdlib theorem'}
(e/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));raise SystemExit(code)
