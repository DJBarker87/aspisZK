import hashlib,json,os,shutil,signal,subprocess,time
from pathlib import Path
root=Path('/tmp/aspis-r1-qm31-arithmetic-20261015')
kit=root/'input'; out=root/'attempt-a'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((kit/'source-pins.json').read_text())
for name,pin in pins['inputs'].items():
 assert sha(kit/name)==pin['sha256']
 if pin['origin']:assert sha(Path(pin['origin']))==pin['sha256']
tp=json.loads((kit/'tool-pins.json').read_text())
for tool in tp['tools']:assert sha(Path(tool['path']))==tool['sha256']
out.mkdir();shutil.copytree(kit,out/'input');shutil.copy2(__file__,out/'run-extraction.py')
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=str(root/'target'),NO_DNA='1')
(out/'environment.json').write_text(json.dumps({k:env[k] for k in ['RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','CARGO_TARGET_DIR','NO_DNA']},indent=2)+'\n')
commands=json.loads((kit/'expected-commands.json').read_text())
def run(label,cmd):
 start=time.monotonic();peak=0;killed=False
 with (out/(label+'.log')).open('x') as log:
  p=subprocess.Popen(['/usr/bin/time','-l',*cmd],cwd=out/'input',env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  while p.poll() is None:
   ps=subprocess.check_output(['ps','-axo','pid=,pgid=,rss='],text=True)
   rss=sum(int(z[2]) for line in ps.splitlines() if len(z:=line.split())==3 and int(z[1])==p.pid)
   peak=max(peak,rss)
   if rss>2*1024*1024 or time.monotonic()-start>300:
    killed=True;os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.1)
  code=p.wait()
 rec={'label':label,'command':cmd,'exit_status':code,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_process_group_rss_kib_sampled':peak,'stop_threshold_kib':2*1024*1024,'timeout_seconds':300,'killed_for_memory_or_timeout':killed,'source_revision':pins['proof_worktree_head'],'runner_sha256':sha(Path(__file__)),'note':'Small local standalone extraction, no dependency build; sampled stop threshold, no cgroup. Process swaps in log. Not a proof replay or source call-site refinement.'}
 (out/(label+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)
 if code:raise SystemExit(code)
run('lock',['cargo','generate-lockfile','--offline'])
rewrite=lambda s:s.replace(str(root/'output'),str(out))
run('charon',[rewrite(s) for s in commands['charon']])
run('aeneas',[rewrite(s) for s in commands['aeneas']])
(out/'artifact-pins.json').write_text(json.dumps({str(p.relative_to(out)):sha(p) for p in out.rglob('*') if p.is_file()},indent=2)+'\n')
