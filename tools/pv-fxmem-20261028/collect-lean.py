"""Read-only capture of an existing shared-launcher attempt."""
from pathlib import Path
import json,subprocess,sys,re,time,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
n=int(sys.argv[1]);assert 35500<=n<=35599
code=f'''from pathlib import Path
import json
b=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
print(json.dumps({{name:(b/(prefix+'-{n}.'+suffix)).read_text() if (b/(prefix+'-{n}.'+suffix)).exists() else None for name,prefix,suffix in [('output.log','out','log'),('time.log','time','log'),('sha.txt','sha','txt')]}}))
'''
for retry in range(1,11):
 r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True)
 if r.returncode==0:break
 with (E/'transport.jsonl').open('a') as f:f.write(json.dumps(dict(operation='read-only Lean receipt recovery',id=n,exit=r.returncode,error=r.stderr,retry=retry,epoch=time.time()))+'\n')
 if r.returncode!=255 or retry==10:raise SystemExit(r.returncode)
 time.sleep(60)
x=json.loads(r.stdout)
assert x['time.log'] is not None and x['output.log'] is not None,x
for name,s in x.items():
 if s is not None:(E/f'{n}-{name}').write_text(s)
tim=x['time.log'];log=x['output.log']
def field(label):
 a=re.search(label+r':\s*(.+)',tim);return a[1] if a else None
j=json.loads((E/f'{n}-submission.json').read_text())
a=re.findall(r'^exit=(\d+)',log,re.M);assert a
j.update(target=json.loads((E/f'{n}-command.json').read_text()),exit=int(a[-1]),wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\)'),peak_rss_kib=field(r'Maximum resident set size \(kbytes\)'),swap=field('Swaps'),axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S),limits=dict(Lean_M=7000,MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=128 if n<=35501 else 64),errors=re.findall(r'.*error:.*',log))
j['accepted']=j['exit']==0 and 'sorryAx' not in log and len(j['axioms'])==len(re.findall(r'^#print axioms ',(E/f'{n}-source.lean.txt').read_text(),re.M))
(E/f'{n}.json').write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps({k:j[k] for k in ['id','exit','wall','peak_rss_kib','swap','accepted']}))
