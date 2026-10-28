"""One sequential optimized native control, with unchanged admission and caps."""
from pathlib import Path
import subprocess,sys,shlex,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028'
H='/home/dombarker/project-offloads/codex-pv-l2d-20261028';host='dombarker@100.108.41.90'
label=sys.argv[1];assert re.fullmatch(r'[a-z0-9-]+',label)
s=R/'tools/pv-l2d-20261028'/(label+'.rs');rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert subprocess.check_output(['git','show',rev+':'+str(s.relative_to(R))])==s.read_bytes()
def ssh(c):return subprocess.run(['ssh',host,c],text=True,capture_output=True)
q=ssh(f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {H}/admission-{label}.json > {H}/admission-{label}.log 2>&1\npv_status=$?\ncat {H}/admission-{label}.log\nexit $pv_status')
(E/f'admission-{label}.log').write_text(q.stdout+q.stderr);a=json.loads(q.stdout.strip().splitlines()[-1])
if q.returncode!=0 or not a['allowed']:print('REFUSED',a);sys.exit(78)
q=subprocess.run(['scp','-q',str(s),host+':'+H+'/'+label+'.rs']);assert q.returncode==0
cmd=['systemd-run','--user','--scope','--quiet','--unit=pv-l2d-'+label,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+'/time-'+label+'.log','sh','-c',f'/home/dombarker/.cargo/bin/rustup run 1.94.1 rustc -O --edition=2021 -C codegen-units=1 -C link-arg=-Wl,--threads=4 {H}/{label}.rs -o {H}/{label} && {H}/{label}']
v=dict(target=label,command=cmd,source_revision=rev,source_sha256=hashlib.sha256(s.read_bytes()).hexdigest(),admission=a,expected_time='optimized standalone compilation, then finite public index/byte control-flow validation; no chained field arithmetic',print_axioms='N/A: Rust finite validation',features='standalone exact-body comparator; no crate feature or deployed-ELF credit')
(E/f'launch-{label}.json').write_text(json.dumps(v,indent=2)+'\n')
q=ssh(shlex.join(cmd)+f' > {H}/out-{label}.log 2>&1');v['scope_exit']=q.returncode
(E/f'transport-{label}.json').write_text(json.dumps(dict(exit=q.returncode,stdout=q.stdout,stderr=q.stderr),indent=2)+'\n')
for kind in ['out','time']:
 q=ssh(f'cat {H}/{kind}-{label}.log');assert q.returncode==0,q.stderr;(E/f'{kind}-{label}.log').write_text(q.stdout)
t=(E/f'time-{label}.log').read_text();o=(E/f'out-{label}.log').read_text();print(o);print(t)
v.update(exit=int(re.search(r'Exit status: (\d+)',t)[1]),wall=re.search(r'Elapsed.*: (\S+)',t)[1],peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',t)[1]),swaps=int(re.search(r'Swaps: (\d+)',t)[1]),caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
(E/f'receipt-{label}.json').write_text(json.dumps(v,indent=2)+'\n');sys.exit(v['exit'])
