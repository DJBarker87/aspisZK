from pathlib import Path
import os,subprocess,hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit21-20261021');name='tail-runtime-v1'
p=H/'src/crates/aspis-r1-cost-probe/src/sim.rs';s=p.read_text();assert 'mod tail_tests21' not in s;p.unlink();p.write_text(s+'\n'+(H/'harness/tail-tests21.rs').read_text())
caps=[]
for q in Path('/sys/fs/cgroup').rglob('memory.max'):
 try:
  v=q.read_text().strip()
  if v!='max' and (q.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(q.parent),bytes=int(v)))
 except OSError:pass
assert sum(x['bytes'] for x in caps)+8*2**30<=55*2**30
os.chdir(H/'src');os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_TARGET_DIR=str(H/'charon-target'),CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4 --cfg aeneas_ref')
(H/(name+'-inputs.json')).write_text(json.dumps(dict(source_revision='ec5946193',reservations=caps,source_hashes={str(p.relative_to(H/'src')):hashlib.sha256(p.read_bytes()).hexdigest() for p in (H/'src').rglob('*.rs')},scope='Two deterministic differential fixtures; full request/answer histories and serialized trace; not universal refinement'),indent=2)+'\n')
subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/name),'Optimized compilation then two differential transcript fixtures; no dense arithmetic','--','cargo','test','--release','--locked','--offline','-j','4','-p','aspis-r1-cost-probe','--features','r1p-check','--lib','sim::tail_tests21','--','--nocapture'],check=True)
