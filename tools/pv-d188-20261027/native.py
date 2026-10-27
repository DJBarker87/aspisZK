import subprocess,json,shlex,time,hashlib,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-d188-20261027';host='dombarker@100.108.41.90';base='/home/dombarker/project-offloads/codex-pv-d188-20261027';tag=sys.argv[1] if len(sys.argv)>1 else 'native-001'
def ssh(s):return subprocess.run(['ssh',host,s],capture_output=True,text=True)
gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
r=ssh(f'python3 {gate} {base}/{tag}-admission.json > {base}/{tag}-reservation.log 2>&1; status=$?; cat {base}/{tag}-reservation.log; exit $status');(out/f'{tag}-admission.log').write_text(r.stdout+r.stderr)
assert r.returncode==0 and json.loads(r.stdout)['allowed'] is True,r.stdout+r.stderr
rel={'native-001':'native.rs','native-002':'native2-files/native2.rs','native-003':'native2-files/native3.rs','native-004':'native2-files/native3.rs','native-005':'native2-files/native4.rs','native-006':'native2-files/native5.rs','native-007':'native2-files/native6.rs','native-008':'native2-files/native7.rs'}[tag]
src=out/'tests'/rel
if '/' in rel:subprocess.run(['scp','-r',str(src.parent),f'{host}:{base}/'],check=True,capture_output=True)
else:subprocess.run(['scp',str(src),f'{host}:{base}/native.rs'],check=True,capture_output=True)
remote_src=base+'/'+rel

inner=shlex.join(['/home/dombarker/.cargo/bin/rustc','--edition=2021','-O',remote_src,'-o',base+'/native'])+' && '+shlex.quote(base+'/native')
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',base+'/'+tag+'-time.log','sh','-c',inner]
(out/f'{tag}-command.json').write_text(json.dumps(dict(command=cmd,expected_time='tiny optimized compilation and scalar/slice fixture execution; no elimination or proof generation'),indent=2)+'\n')
t=time.time();r=ssh(shlex.join(cmd));wall=time.time()-t;(out/f'{tag}-out.log').write_text(r.stdout+r.stderr)
tm=ssh('cat '+base+'/'+tag+'-time.log');(out/f'{tag}-time.log').write_text(tm.stdout+tm.stderr)
import re
rec=dict(target='exact copied native field/sampler bodies',exit=r.returncode,wall_seconds=wall,peak_rss_kib=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',tm.stdout),swaps=re.findall(r'Swaps: (\d+)',tm.stdout),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),print_axioms='N/A native tests',caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
(out/f'{tag}-receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(r.stdout+r.stderr);print(json.dumps(rec))
