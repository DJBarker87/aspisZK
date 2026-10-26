from pathlib import Path
import subprocess,json,re,hashlib
R=Path(__file__).resolve().parents[2];D=R/'evidence/pv-l2-sim-20261026';H='dombarker@100.108.41.90';remote='/home/dombarker/project-offloads/codex-pv-l2-sim-20261026'
version=subprocess.check_output(['ssh',H,'/home/dombarker/.cargo/bin/kani --version'],text=True).strip()
source=R/'tools/pv-l2-sim-20261026/PV_L2_native.rs';sha=hashlib.sha256(source.read_bytes()).hexdigest()
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for i in range(1,21):
 name=f'k{i:02d}';d=D/name;d.mkdir(exist_ok=True)
 for kind in ['out','time','exit','target','reservation']:
  suffix='txt' if kind in ['exit','target'] else 'log'
  q=subprocess.run(['ssh',H,f'cat {remote}/{kind}-{name}.{suffix}'],capture_output=True)
  if q.returncode==0:(d/(kind+'.log')).write_bytes(q.stdout)
 out=(d/'out.log').read_text();time=(d/'time.log').read_text()
 target=(d/'target.log').read_text().strip() if i>1 else 'F5_stop_count'
 status=int((d/'exit.log').read_text()) if i>1 else 0
 def metric(label):
  x=re.search(re.escape(label)+r':\s*(\d+)',time);return int(x[1]) if x else None
 r={'attempt':i,'target':target,'source_sha256':sha,'source_revision':rev,'source_revision_note':'baseline during all Kani runs; proof-local source pinned by hash','dependency_fingerprint':version+' standalone bundled sysroot','exit':status,'wall':re.search(r'Elapsed.*: (\S+)\s*$',time,re.M)[1], 'gnu_time_reported_peak_rss_kib':metric('Maximum resident set size (kbytes)'),'peak_rss_kib':None if status==124 else metric('Maximum resident set size (kbytes)'),'swaps':metric('Swaps'),'print_axioms':'N/A: Kani','result':'passed' if status==0 else 'timeout' if status==124 else 'failed','scope':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64},'rss_note':'timeout wrapper RSS can undercount descendants; null peak intentionally retained on timeouts','expected_work':'Kani compilation then named bounded symbolic CBMC harness; no dense arithmetic gate','stubs':False}
 (d/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
 print(name,target,r['result'])
subprocess.run(['scp',f'{H}:{remote}/reservation-k18-retry.json',str(D/'reservation-k18-retry.json')],check=True)
