"""Read-only host receipts and post-run dependency/source fingerprints."""
from pathlib import Path
import subprocess,json,hashlib,re,shlex
OUT=Path(__file__).resolve().parent
HOST='dombarker@100.108.41.90'
T='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/'
def read(path):
 return subprocess.check_output(['ssh',HOST,'cat '+shlex.quote(path)],text=True)
module={20000:'Statement',20001:'Statement',20002:'Readable',20003:'Fields',20004:'FieldsComplete',20005:'Consumers'}
receipts=[]
for attempt,suffix in module.items():
 source='PV_Ledger_'+suffix+'.lean';s=(OUT/source).read_bytes();log=read(T+f'out-{attempt}.log');(OUT/({20000:'out-20000.log',20001:'statement-20001.log',20002:'readable-20002.log',20003:'rejected-fields-20003.log',20004:'fields-20004.log',20005:'consumers-20005.log'}[attempt])).write_text(log)
 try:tim=read(T+f'time-{attempt}.log')
 except subprocess.CalledProcessError:tim=''
 if tim:(OUT/f'time-{attempt}.log').write_text(tim)
 matches=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S)
 def metric(pattern):
  m=re.search(pattern,tim);return m.group(1) if m else None
 rec=dict(attempt=attempt,module=source,source_sha256=hashlib.sha256(s).hexdigest(),source_revision='e654849fd1aacaacecd0c19a6937bbe6136a222f',source_tree_dirty=True,input_revision=json.loads((OUT/'input-pins.json').read_text())['revision'],source_kind='new print/check-only helper retained verbatim; no theorem',command=f'sh /home/dombarker/project-offloads/codex-pv-ledger-20261026/run-joint.sh {attempt} {source[:-5]} J 7000 8'+(' '+(OUT/'statement-fingerprint.txt').read_text().strip() if attempt==20001 else ''),exit_status=metric(r'Exit status: (\d+)'),wall=metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.*)'),peak_rss_kib=metric(r'Maximum resident set size \(kbytes\): (\d+)'),swap=metric(r'Swaps: (\d+)'),limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000),print_axioms=matches,errors=[line for line in log.splitlines() if re.search(r': error(?:\(|:)|Traceback \(most recent call last\)|AssertionError:', line)][:15],evidence={20000:'out-20000.log',20001:'statement-20001.log',20002:'readable-20002.log',20003:'rejected-fields-20003.log',20004:'fields-20004.log',20005:'consumers-20005.log'}[attempt])
 if attempt==20000:rec.update(compiler_invoked=False,exit_status=None,reason='barrier FileNotFoundError for unrelated vanished cgroup before GNU time/Lean; limits verified in traceback; permitted one retry after >30s; launcher final grep exit2 is not Lean status')
 else:rec['compiler_invoked']=True
 rec['dependency_fingerprint']='none at launcher' if attempt!=20001 else (OUT/'statement-fingerprint.txt').read_text().strip()
 rec['dependency_note']='Post-run hashes below are a read-only cache snapshot, not launch-time coherence evidence; no full dependency rebuild.'
 receipts.append(rec)
(OUT/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
# Only source/header traversal and SHA256. No Lean compiler or build.
remote=r'''
from pathlib import Path
import json,re,hashlib
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
queue=['R1Z.PrivacyR1HeadlineDeployedReal','R1Z.ProverCommitPublicNonce40','R1Z.ProverCommitLedger36','R1Z.ProverCommitTrustedStd24'];seen={}
while queue:
 m=queue.pop()
 if m in seen:continue
 s=J/'sources'/Path(*m.split('.')).with_suffix('.lean');o=J/'objects'/Path(*m.split('.')).with_suffix('.olean')
 if not s.exists():continue
 b=s.read_bytes();imports=re.findall(r'^import\s+([\w.]+)',b.decode(),re.M)
 seen[m]={'source_sha256':hashlib.sha256(b).hexdigest(),'object_sha256':hashlib.sha256(o.read_bytes()).hexdigest() if o.exists() else None,'imports':imports};queue.extend(imports)
env=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json')
print(json.dumps({'scope':'post-run project-source import closure only; cached objects, not coherent release replay','modules':seen,'env_sha256':hashlib.sha256(env.read_bytes()).hexdigest(),'lean_binary_sha256':hashlib.sha256(Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean').read_bytes()).hexdigest()},indent=2))
'''
(OUT/'host-readonly-capture.py.txt').write_text(remote)
raw=subprocess.check_output(['ssh',HOST,'python3 -c '+shlex.quote(remote)],text=True);(OUT/'host-postrun-pins.json').write_text(raw)
host=json.loads(raw)['modules']; compare=[]
for r in json.loads((OUT/'source-index.json').read_text()):
 if r['origin']!='input revision':continue
 path=r['path'];m=(path.split('/lean/')[1][:-5]).replace('/','.')
 h=host.get(m,{}).get('source_sha256');compare.append(dict(module=m,local=r['sha256'],host=h,equal=h==r['sha256']))
(OUT/'source-host-comparison.json').write_text(json.dumps(compare,indent=2)+'\n')
print('compilers',sum(r['compiler_invoked'] for r in receipts),'of15; Kani0; postrun project modules',len(host),'source mismatches',[r['module'] for r in compare if not r['equal']])
