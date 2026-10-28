"""Submit the native scalar/refill differential; no Kani evidence is involved."""
from pathlib import Path
import json,subprocess,shlex,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028/coins-v1';E.mkdir(parents=True,exist_ok=True);H='/home/dombarker/project-offloads/codex-pv-l2d-20261028';host='dombarker@100.108.41.90'
q=subprocess.run(['ssh',host,f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {H}/admission-coins-v1.json > {H}/admission-coins-v1.log 2>&1\npv_status=$?\ncat {H}/admission-coins-v1.log\nexit $pv_status'],text=True,capture_output=True);(E/'admission-coins-v1.log').write_text(q.stdout+q.stderr);a=json.loads(q.stdout.strip().splitlines()[-1]);assert q.returncode==0 and a['allowed'],a
subprocess.run(['ssh',host,f'mkdir -p {H}/evidence/coins-v1'],check=True)
for p in ['coins-native','coins-cargo-run.py']:
 q=subprocess.run(['scp','-rq',str(R/'tools/pv-l2d-20261028'/p),host+':'+H+'/']);assert q.returncode==0
cmd=['systemd-run','--user','--scope','--quiet','--unit=pv-l2d-coins-v1','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+'/evidence/coins-v1/time-coins-native.log','timeout','300','python3',H+'/coins-cargo-run.py']
v=dict(target='native coins next/m31/qm31 finite controls',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256((R/'tools/pv-l2d-20261028/coins-native/src/main.rs').read_bytes()).hexdigest(),command=cmd,admission=a,expected_time='optimized zeroize/harness compilation, then named scalar/refill/limb-propagation finite controls; no chained field arithmetic',print_axioms='N/A: native finite validation',features='standalone field declarations/constructor and source-identical coins; deployed feature/ELF credit not claimed')
(E/'launch-coins-native.json').write_text(json.dumps(v,indent=2)+'\n');q=subprocess.run(['ssh',host,shlex.join(cmd)+f' > {H}/evidence/coins-v1/out-coins-native.log 2>&1'],text=True,capture_output=True);v['scope_exit']=q.returncode
for name in ['time-coins-native.log','out-coins-native.log','coins-phases.json','dependency-source-check.json','coins-metadata.out','coins-positive.out','coins-positive.err','coins-negative.out','coins-negative.err','coins-build.out','coins-build.err','rustc-version.out','rustc-version.err']:
 r=subprocess.run(['scp','-q',host+':'+H+'/evidence/coins-v1/'+name,str(E/name)],capture_output=True,text=True)
 if r.returncode:print('UNRESOLVED fetch',name,r.returncode,r.stderr)
q=subprocess.run(['scp','-q',host+':'+H+'/coins-native/Cargo.lock',str(R/'tools/pv-l2d-20261028/coins-native/Cargo.lock')]);assert q.returncode==0
out=(E/'out-coins-native.log').read_text();tim=(E/'time-coins-native.log').read_text();print(out);print(tim)
v.update(exit=int(re.search(r'Exit status: (\d+)',tim)[1]),wall=re.search(r'Elapsed.*: (\S+)',tim)[1],peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',tim)[1]),swaps=int(re.search(r'Swaps: (\d+)',tim)[1]),caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
(E/'receipt-coins-native.json').write_text(json.dumps(v,indent=2)+'\n');raise SystemExit(v['exit'])
