"""Collect existing evidence only. Never runs a prover/compiler."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[4]
HOST='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-cx-real-r3-20261023/evidence'
subprocess.run(['rsync','-a','--exclude=RealR3_native','--exclude=kani-target',HOST+':'+H+'/receipts/',str(E/'receipts')+'/'],check=True)
available=subprocess.check_output(['ssh',HOST,'ls '+H+'/111*-input.json'],text=True).splitlines()
for remote in available:
 a=int(Path(remote).name.split('-')[0])
 p=E/(str(a)+'-input.json')
 # input availability decides what ran, not an attempted range census.
 for f in [f'{a}-input.json',f'{a}-launcher.log',f'lean-snapshots/{a}.lean.txt']:
  q=E/f;q.parent.mkdir(parents=True,exist_ok=True)
  subprocess.run(['scp','-q',HOST+':'+H+'/'+f,str(q)],check=True)
 for kind in ['out','time','sha']:
  f=f'{kind}-{a}.'+('txt' if kind=='sha' else 'log')
  subprocess.run(['scp','-q',HOST+':/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/'+f,str(E/f)],check=True)
for f in ['snapshots','*-inputs.json']:
 subprocess.run(['rsync','-a',HOST+':'+H+'/'+f,str(E)+'/'],check=False)
rows=[]
for p in sorted(E.glob('111*-input.json')):
 a=int(p.name.split('-')[0]);i=json.loads(p.read_text());o=(E/f'out-{a}.log').read_text();t=(E/f'time-{a}.log').read_text();s=(E/'lean-snapshots'/f'{a}.lean.txt').read_bytes()
 def val(pat):return re.search(pat,t).group(1).strip()
 axioms=re.findall(r"^'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",o,re.M)
 module=re.search(r'namespace R1Z\.(\w+)',s.decode())[1]
 rows.append(dict(attempt=a,**i,module='R1Z.'+module,command=f'sh RealR3_run-joint.sh {a} R1Z/{module} J 7000 8 {i["deps_fingerprint"]}',exit=int(re.search(r'^exit=(\d+)',o,re.M)[1]),wall=val(r'Elapsed .*: (\S+)'),peak_rss_kib=int(val(r'Maximum resident set size \(kbytes\): (\d+)')),swaps=int(val(r'Swaps: (\d+)')),axioms=axioms,errors=[l for l in o.splitlines() if 'error:' in l or 'error(' in l],memory_high_gib=6,memory_max_gib=8,memory_swap_max=0,tasks_max=64,lean_memory_limit_mb=7000,snapshot_sha256=hashlib.sha256(s).hexdigest()))
(E/'RealR3_attempts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
print(json.dumps([{k:r[k] for k in ['attempt','exit','wall','peak_rss_kib','swaps']} for r in rows],indent=2))
