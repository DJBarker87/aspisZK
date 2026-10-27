"""Retain read-only native proof/extraction receipts; does not launch jobs."""
from pathlib import Path
import subprocess,json,re,hashlib,sys
root=Path(__file__).resolve().parents[2]
name=sys.argv[1];assert re.fullmatch(r'[a-z0-9-]+',name)
base='/home/dombarker/project-offloads/codex-pv-cblib-20261027'
out=root/'evidence/pv-cblib-20261027'/name;out.mkdir(exist_ok=True)
code='''from pathlib import Path
import json,hashlib
p=Path(%r)
names=[x.name for x in p.iterdir() if x.suffix=='.log' or x.name.startswith('input-hashes')]
r={'files':{n:(p/n).read_text() for n in names}}
for n in ['admission-barrier.json','admission-before.json']:
 if (p/n).exists():
  s=json.loads((p/n).read_text());r[n]={k:v for k,v in s.items() if k not in ['cgroups','uncapped_background']}
r['inputs']={}
for n in %r:
 q=Path(n)
 if q.exists():r['inputs'][n]={'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'size':q.stat().st_size}
print(json.dumps(r))
'''%(base+'/'+name,[base+'/proof/lib.rs',base+'/proof/reference.rs',base+'/proof/Cargo.toml',base+'/PV_CB_TakeRef.llbc',base+'/take-generated/Funs.lean',*[base+'/'+x for x in sys.argv[2:]]])
data=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-c',__import__('shlex').quote(code)],text=True))
for n,s in data.pop('files').items():(out/n).write_text(s)
t=(out/'time.log').read_text() if (out/'time.log').exists() else ''
def metric(k):
 m=re.search(re.escape(k)+r':\s*(.+)',t);return m[1] if m else None
barrier=data.get('admission-barrier.json',{})
r=dict(target=barrier.get('command'),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),source_identity='post-run read-only input hashes; candidate-snapshot.json identifies the frozen Rust snapshot; source-provenance.json identifies pinned third-party library files. No attribution to a different candidate or deployed ELF.',exit=metric('Exit status'),wall=metric('Elapsed (wall clock) time (h:mm:ss or m:ss)'),peak_rss_kib=metric('Maximum resident set size (kbytes)'),swap=metric('Swaps'),print_axioms='N/A native gate or extraction; Lean audits have separate numbered receipts',attempt_charged=bool(t),limits=barrier.get('limits'),inputs=data['inputs'],dependency_fingerprint=hashlib.sha256(json.dumps(data['inputs'],sort_keys=True).encode()).hexdigest(),admissions={k:v for k,v in data.items() if k.startswith('admission')})
(out/'collected-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
with (out/'collection-history.jsonl').open('a') as f:f.write(json.dumps(r,sort_keys=True)+'\n')
print(name,'charged',r['attempt_charged'],'exit',r['exit'])
