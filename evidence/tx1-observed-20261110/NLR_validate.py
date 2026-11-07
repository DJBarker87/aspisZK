"""Own strict source/native manifest preflight; no host infrastructure mutation."""
from pathlib import Path
import json,re,hashlib,subprocess,sys
E=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(f.read_text())for f in E.glob('NLR_[LK][0-9][0-9][0-9]/receipt.json')]
assert len({r['attempt']for r in rows})==len(rows)
assert sum(r['kind']=='kani'for r in rows)<=40
assert sum(r['attempt'][4]=='L'for r in rows)<=140
latest={}
for r in sorted(rows,key=lambda x:x['attempt']):
 required=['attempt','module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','deps_fingerprint','print_axioms']
 assert all(k in r for k in required),(r['attempt'],'section6 fields missing')
 if r['kind']!='lean' or r['exit_status'] or not str(r.get('module','')).startswith('NLR_'):continue
 m=r['module'];p=E/'NLR_generated'/(m+'.lean');q=E/r['attempt']/'sources/NLR_generated'/(m+'.lean')
 if p.is_file()and q.is_file()and p.read_bytes()==q.read_bytes():latest[m]=r
standard={'propext','Classical.choice','Quot.sound'};tops=[]
for m,r in latest.items():
 s=(E/'NLR_generated'/(m+'.lean')).read_text()
 assert not re.search(r'(^|\n)\s*(axiom|sorry|admit)\b|native_decide|set_option max(?:Heartbeats|RecDepth)',s),(m,'forbidden proof input')
 for n in re.findall(r'^theorem\s+([\w]+)',s,re.M):assert '#print axioms '+n in s,(m,n,'axiom directive absent')
 for line in r['print_axioms']:
  if 'depends on axioms:' in line:
   ax={n.strip()for n in line.split('[',1)[1].split(']',1)[0].split(',')if n.strip()};assert ax<=standard,(m,line)
  tops.append(line)
for n in range(1,41):
 a=f'NLR_K{n:03d}';p=E/a/'receipt.json'
 if not p.exists():continue
 assert json.loads((E/(a+'-graph-check.json')).read_text())['graph_matches_frozen']
 assert json.loads((E/(a+'-lock-check.json')).read_text())['unchanged']
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,(str(p),'file exceeds20MB')
r=subprocess.run(['git','diff','--quiet','--','crates','programs','Cargo.lock']);assert r.returncode==0,'shipped file changed'
out=dict(status='PASS',modules=len(latest),selected=list(latest),axiom_lines=len(tops),native_graphs_checked=sum(r['kind']=='kani'for r in rows),lean_support_consumed=sum(r['attempt'][4]=='L'for r in rows),closed_rows=0,schemas_source_value_only=True,full_child136_packet=False)
(E/'NLR_PREFLIGHT.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items()if k!='selected'}))
