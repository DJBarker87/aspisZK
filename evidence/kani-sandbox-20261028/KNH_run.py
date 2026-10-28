from KNH_host import *
import sys,fcntl
lock=(E/'KNH_SERIAL.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
version,index=sys.argv[1:];index=int(index)
plan=json.loads((E/'KNH_PLAN.json').read_text());item=plan[index-1]
a=f'KNH_{"N" if version=="new" else "O"}{index:03d}'
assert not (E/(a+'.json')).exists(),'Never resubmit a submitted attempt'
if version=='new':assert len(list(E.glob('KNH_N[0-9][0-9][0-9].json')))<40
else:assert len(list(E.glob('KNH_O[0-9][0-9][0-9].json')))<10
expected='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
scratch=B+'/KNH_scratch'
r=py('''from pathlib import Path
import hashlib,json,shutil
b=Path(%r);s=b/'KNH_scratch';p=s/'Cargo.lock'
sha=hashlib.sha256(p.read_bytes()).hexdigest();assert sha==%r
shutil.copyfile(b/%r,s/'KNH_probe.rs')
print(json.dumps(dict(lock_before_sha256=sha,external_packages=[],external_edges=[],resolution='standalone rustc, no Cargo resolver invoked',frozen_lock_exact=True,source_sha256=hashlib.sha256((s/'KNH_probe.rs').read_bytes()).hexdigest())))
'''%(B,expected,item['source']));assert r.returncode==0,r.stderr
check=json.loads(r.stdout);check['frozen_source_revision']='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
(E/(a+'-graph-check.json')).write_text(json.dumps(check,indent=2)+'\n')
env={'TMPDIR':B+'/KNH_tmp','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','RUSTFLAGS':'-C opt-level=3 -C overflow-checks=on -C link-arg=-Wl,--threads=1','PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'}
if version=='new':
 install=json.loads((E/'KNH_INSTALL.json').read_text());env.update(install['env']);driver=install['driver']
else:driver='/home/dombarker/.kani/kani-0.67.0/bin/kani-driver'
cmd=[driver,scratch+'/KNH_probe.rs','-Z','unstable-options','-Z','stubbing','--harness-timeout','90s','--output-format','regular','--harness',item['harness']]
if item.get('exact',True):cmd+=['--exact']
if item['group']=='shape':cmd+=['-Z','function-contracts']
if item['group']=='loop':cmd+=['-Z','loop-contracts']
# Bounded standalone harnesses; pass explicit optimization via rustc flags.
cmd+=['--','-C','opt-level=3','-C','overflow-checks=on','-C','link-arg=-Wl,--threads=1']
rc=launch(dict(attempt=a,kind='kani',tool_version=version,target=item,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,sources=['KNH_scratch/KNH_probe.rs','KNH_scratch/KMX_stubs.rs','KNH_scratch/Cargo.lock'],command=cmd,env=env,timeout=600 if item['group']!='copy' else 2400,expected_time='Optimized standalone code generation, then '+item['group']+' diagnostic; no frozen proof credit',deps_fingerprint=check,print_axioms='N/A: no Lean'))
r=py('''from pathlib import Path
import hashlib,json
s=Path(%r)
print(json.dumps(dict(lock_after_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest())))
'''%scratch);assert r.returncode==0;check.update(json.loads(r.stdout));check['lock_unchanged']=check['lock_after_sha256']==expected
(E/(a+'-graph-check.json')).write_text(json.dumps(check,indent=2)+'\n');assert check['lock_unchanged'],'STOP lock drift'
# Always remove only this attempt's private solver debris, retain evidence and persistent cache.
r=py('''from pathlib import Path
import json
root=Path(%r);removed=[]
for p in root.rglob('*'):
 if p.is_file() and ((p.name.startswith('external-sat') and p.suffix=='.cnf') or p.name.startswith('smt2_dec_problem')):
  removed.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
print(json.dumps(removed))
'''%(B+'/KNH_tmp'));assert r.returncode==0;(E/(a+'-solver-cleanup.json')).write_text(r.stdout)
